(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMsnprintfSeamI.v (a working branch 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan by reloc.py (target disco-A): module paths changed; 4 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-A.tsv); GXA symbol keys kept (0x22e18, 0x34288, 0x7f000400); names: record RT_IImgA -> A_img RecAsanVfA.N_img_asan_vf; hand checks: FMgxa_mem STOP: names differ: fm FMgxa_mem.copy_ready/set_ready = disco lib/<img>/RT_gxa_calls_mem.copy_ready/set_ready; fm memcpy_stack_contract_A/memset_stack_contract_A (at A_img) = disco lib/<img>/RT_gxa_calls_mem_vf.memcpy_stack_contract_Avf/_Avf (Y: _Bvf); map each use by hand. *)
(* THE GXA SEAM AT fm.asan's MUSL VFPRINTF, INSTANTIATED: FMgxaSeam.fm_vfprintf_seam with fm's three interceptor
   call contracts (FMgxa_mem.memcpy_stack_contract_A, FMgxa_mem.memset_stack_contract_A,
   RT_gxa_strnlen.strnlen_stack_contract_A) and their ready predicates, fm's format family pf_family_ro
   pf_fm_piece over [0x10000, 0x9a638) (the image data below the GOT slot of __stack_chk_guard), and fm's cells:
   the stack-protector GOT slot and guard, sn_write and musl vfprintf, each the symbol GXA names (checked by
   vm_compute). READY, the readiness the seam takes, is discharged in FMgxaSeamFm.v, so this file takes no
   hypothesis for it. No function is proved here: this file instantiates the proved seam. New file. *)
(* Modified by a Theorem Labs lane on a working branch: uses fm_vfprintf_seam_closed; READY moved to the per-call store. *)
(* Modified by a Theorem Labs lane (R-1 W0): fm_seam_instP, the same for any covered-piece predicate PK with its seam arms; fm_seam_inst is its instance. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import AB1v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnUpoison PfFacts SnShared SnSx.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require AF0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA Require
AsanFacts CopyCall SetCall StrnlenCall G_printf_core_common G_vfprintf_snf.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.I Require Import RecAsanVfA.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnFF.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require Import FMgxaSeamGuard.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require
FMgxaSeamNorm FMgxaSeamPf FMgxaSeam FMgxaSeamFm RT_gxa_strnlen FMH_Base FMsnprintfImg.
Import ListNotations.
Local Open Scope Z_scope.

(* the module aliases of FMgxaSeam.v *)
Module GXC := OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GAF := OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.AsanFacts.
Module GVA := OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GCA := OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module NM := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.FMgxaSeamNorm.

#[local] Existing Instance N_img_asan_vf.

(* ---- fm's cells and code addresses are the symbols GXA names on fm.asan ---- *)
Lemma si_got : FMH_Base.FM_GOT_canary = @sym N_img_asan_vf 0x22e18.
Proof. vm_compute. reflexivity. Qed.
Lemma si_guard : FMH_Base.FM_canary = @sym N_img_asan_vf 0x34288.
Proof. vm_compute. reflexivity. Qed.
Lemma si_snw : FMsnprintfImg.A_SNW = @sym N_img_asan_vf GXC.K_SN_WRITE.
Proof. vm_compute. reflexivity. Qed.
Lemma si_vfp : FMsnprintfImg.A_VFP = @sym N_img_asan_vf 0x7f000400.
Proof. vm_compute. reflexivity. Qed.
(* the family's range: from the image's first byte to the GOT slot *)
Lemma si_fam_lo : 65536 <= 0x10000.
Proof. lia. Qed.
Lemma si_fam_hi : 0xa1198 <= @sym N_img_asan_vf 0x22e18.
Proof. rewrite FMgxaSeam.sa_sym_got_ssp. lia. Qed.

Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : AF0m.TfibSyms B.
(* READY is no longer a hypothesis here: FMgxaSeamFm.fm_vfprintf_seam_closed carries it, discharged
   by a Theorem Labs lane's FMgxaSeamReady.seam_ready_holds at fm's three ready predicates *)

(* any covered-piece predicate PK whose pieces have their three seam arms (FMgxaSeamPf.v) *)
Theorem fm_seam_instP : forall (PK : pf_piece -> Prop),
  (forall p, PK p -> FMgxaSeamPf.seam_text_arm p) -> (forall p, PK p -> FMgxaSeamPf.seam_pargs_arm p) ->
  (forall p, PK p -> FMgxaSeamPf.seam_bytes_arm p) ->
  forall K img_lo img_hi cr,
  GVA.VFA_DEPTH <= K -> img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_vf <= img_hi -> NM.ro_covered cr ->
  sh_avfprintf_icpt_realizesUx tfibsegs B (pf_family_ro PK 0x10000 0xa1198) K
    FMH_Base.FM_GOT_canary FMH_Base.FM_canary img_lo img_hi cr FMsnprintfImg.A_SNW FMsnprintfImg.A_VFP.
Proof.
intros PK AT AP AB K img_lo img_hi cr HK Hlo Hhi HCOV.
rewrite si_vfp.
exact (FMgxaSeamFm.fm_vfprintf_seam_closedP B LAWS TB PK AT AP AB
  K _ _ img_lo img_hi _ 0x10000 0xa1198 cr HK si_got si_guard si_snw Hlo Hhi si_fam_lo si_fam_hi HCOV).
Qed.

(* fm's pieces *)
Theorem fm_seam_inst : forall K img_lo img_hi cr,
  GVA.VFA_DEPTH <= K -> img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_vf <= img_hi -> NM.ro_covered cr ->
  sh_avfprintf_icpt_realizesUx tfibsegs B (pf_family_ro pf_fm_piece 0x10000 0xa1198) K
    FMH_Base.FM_GOT_canary FMH_Base.FM_canary img_lo img_hi cr FMsnprintfImg.A_SNW FMsnprintfImg.A_VFP.
Proof.
intros K img_lo img_hi cr HK Hlo Hhi HCOV.
exact (fm_seam_instP pf_fm_piece FMgxaSeamPf.pf_fm_text_arms FMgxaSeamPf.pf_fm_pargs_arms
  FMgxaSeamPf.pf_fm_bytes_arms K img_lo img_hi cr HK Hlo Hhi HCOV).
Qed.
End I.
