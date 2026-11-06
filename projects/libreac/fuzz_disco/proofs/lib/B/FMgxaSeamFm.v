(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamFm.v (a working branch 0ddf65fd8cc); relocated to libreac/fuzz_disco.asan-ubsan by reloc.py (target disco-Y): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan-ubsan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-Y.tsv); GXA symbol keys kept (0x22e18, 0x34288, 0x7f000400); names: record RT_IImgA -> A_img RecAsanVfB.N_img_asan_ubsan_vf; A-core -> Y-core (lib.Reusable): AB1v->YB1v, AF0m->YF0m; hand checks: FMgxa_mem STOP: names differ: fm FMgxa_mem.copy_ready/set_ready = disco lib/<img>/RT_gxa_calls_mem.copy_ready/set_ready; fm memcpy_stack_contract_A/memset_stack_contract_A (at A_img) = disco lib/<img>/RT_gxa_calls_mem_vf.memcpy_stack_contract_Avf/_Avf (Y: _Bvf); map each use by hand. *)
(* THE GXA SEAM AT fm.asan's MUSL VFPRINTF, CLOSED: FMgxaSeam.fm_vfprintf_seam with every Section
   hypothesis discharged but the ambient ones (the FP state fx, the run ceiling rc, the symbol
   assignment B with its laws and fm's symbols).

   The three interceptor call contracts and their readiness predicates are fm's own
   (FMgxa_mem.memcpy_stack_contract_A / memset_stack_contract_A at FMgxa_mem.copy_ready /
   set_ready, RT_gxa_strnlen.strnlen_stack_contract_A at RT_gxa_strnlen.strn_ready), all three at
   the image instance RT_IImgA.A_img, the instance fm_vfprintf_seam runs at.  READY, the readiness
   of those three predicates at musl vfprintf's call site, is FMgxaSeamReady.seam_ready_holds.

   No function is proved here and no machine step is walked: this file only instantiates.  New
   file.  R-1 W0: fm_vfprintf_seam_closedP is the same for any covered-piece predicate PK whose pieces
   have their seam arms; fm_vfprintf_seam_closed is its instance at fm's pieces. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnUpoison PfFacts SnShared SnSx.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YF0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA Require G_vfprintf_snf.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.I Require Import RecAsanVfB.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnFF.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require FMgxaSeamNorm FMgxaSeamReady.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A Require FMgxaSeamPf.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.B Require FMgxaSeam RT_gxa_calls_mem RT_gxa_calls_mem_vf RT_gxa_strnlen.
Import ListNotations.
Local Open Scope Z_scope.

Module GXC := OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GVA := OSSVerify.Proofs.libreac.fuzz_disco.lib.CJ.RL.GXA.G_vfprintf_snf.
Module NM := OSSVerify.Proofs.libreac.fuzz_disco.lib.B.FMgxaSeamNorm.
Module SR := OSSVerify.Proofs.libreac.fuzz_disco.lib.B.FMgxaSeamReady.
Module FMM := OSSVerify.Proofs.libreac.fuzz_disco.lib.B.RT_gxa_calls_mem.
Module FMMV := OSSVerify.Proofs.libreac.fuzz_disco.lib.B.RT_gxa_calls_mem_vf.
Module RSN := OSSVerify.Proofs.libreac.fuzz_disco.lib.B.RT_gxa_strnlen.

#[local] Existing Instance N_img_asan_ubsan_vf.

Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : YF0m.TfibSyms B.

(* any covered-piece predicate PK whose pieces have their three seam arms (FMgxaSeamPf.v) *)
Theorem fm_vfprintf_seam_closedP : forall (PK : pf_piece -> Prop),
  (forall p, PK p -> FMgxaSeamPf.seam_text_arm p) -> (forall p, PK p -> FMgxaSeamPf.seam_pargs_arm p) ->
  (forall p, PK p -> FMgxaSeamPf.seam_bytes_arm p) ->
  forall (K gc gv img_lo img_hi snw fam_lo fam_hi : Z) (cr : list (Z * Z)),
    GVA.VFA_DEPTH <= K -> gc = @sym N_img_asan_ubsan_vf 0x22e18 -> gv = @sym N_img_asan_ubsan_vf 0x34288 ->
    snw = @sym N_img_asan_ubsan_vf GXC.K_SN_WRITE -> img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_ubsan_vf <= img_hi ->
    65536 <= fam_lo -> fam_hi <= @sym N_img_asan_ubsan_vf 0x22e18 -> NM.ro_covered cr ->
    sh_avfprintf_icpt_realizesUx tfibsegs B
      (pf_family_ro PK fam_lo fam_hi) K gc gv img_lo img_hi cr snw (@sym N_img_asan_ubsan_vf 0x7f000400).
Proof.
intros PK AT AP AB.
exact (FMgxaSeam.fm_vfprintf_seamP B LAWS TB FMM.copy_ready FMM.set_ready RSN.strn_ready
         FMMV.memcpy_stack_contract_Bvf FMMV.memset_stack_contract_Bvf RSN.strnlen_stack_contract_A
         (SR.seam_ready_holds B LAWS TB) PK AT AP AB).
Qed.

(* fm's pieces *)
Theorem fm_vfprintf_seam_closed :
  forall (K gc gv img_lo img_hi snw fam_lo fam_hi : Z) (cr : list (Z * Z)),
    GVA.VFA_DEPTH <= K -> gc = @sym N_img_asan_ubsan_vf 0x22e18 -> gv = @sym N_img_asan_ubsan_vf 0x34288 ->
    snw = @sym N_img_asan_ubsan_vf GXC.K_SN_WRITE -> img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan_ubsan_vf <= img_hi ->
    65536 <= fam_lo -> fam_hi <= @sym N_img_asan_ubsan_vf 0x22e18 -> NM.ro_covered cr ->
    sh_avfprintf_icpt_realizesUx tfibsegs B
      (pf_family_ro pf_fm_piece fam_lo fam_hi) K gc gv img_lo img_hi cr snw (@sym N_img_asan_ubsan_vf 0x7f000400).
Proof.
exact (fm_vfprintf_seam_closedP pf_fm_piece FMgxaSeamPf.pf_fm_text_arms FMgxaSeamPf.pf_fm_pargs_arms
         FMgxaSeamPf.pf_fm_bytes_arms).
Qed.

End F.
