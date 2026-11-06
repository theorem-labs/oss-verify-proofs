(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import RelocKitOL RelocTacOL CanonImgOL .
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import MuslTac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import RelocImg CanonImg.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF PFBase PFSpec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_LeptStderr () := "c79OSSVerify5KrLib6Common9Leptonica2OL:LeptStderr2LGC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib6Common9Leptonica2OL:LeptStderr;rl_lenv_ok1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl6PFSpecGlept_stderr_s1_contractC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib6Common9Leptonica2OL:LeptStderr;rl_lenv_ok2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common4Musl6PFSpecGlept_stderr_s2_contractC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section Env.
Context {RLOC : Reloc}.
Definition LG : SSP.ls_addrs :=
  {| SSP.ls_entry := (0x13694 + dF_13694); SSP.ls_handler_cell := (0x1f428 + dA_1f3f8); SSP.ls_devnull := (0x1365c + dF_1365c);
     SSP.ls_canary_got := (0x1e3e0 + dA_1e3b8); SSP.ls_canary := (0x2f848 + dA_2f848);
     SSP.ls_img_lo := rl_img_lo; SSP.ls_img_hi := rl_rw_lo;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := rl_img_hi + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [(0x102f1 + dOLS_102f1); (0x1034f + dOLS_1034f); (0x1037f + dOLS_1037f); (0x104e0 + dOLS_104e0); (0x10544 + dOLS_10544); (0x10572 + dOLS_10572); (0x105e4 + dOLS_105e4); (0x10612 + dOLS_10612); (0x10675 + dOLS_10675);
                  (0x106fa + dOLS_106fa); (0x1072f + dOLS_1072f); (0x10781 + dOLS_10781); (0x1083d + dOLS_1083d); (0x10906 + dOLS_10906); (0x10947 + dOLS_10947); (0x1097f + dOLS_1097f)];
     SSP.ls_fmts2 := [(0x10a13 + dS_10a13)];
     SSP.ls_sev_got := (0x1e3b0 + dA_1e3b0); SSP.ls_sev := (0x1f420 + dA_1f3f8) |}.
End Env.

Class RelocLeptEnvOL (RL : Reloc) := {
  rl_lenv_ok1 : ls_ok1 (@LG RL) = true;
  rl_lenv_ok2 : ls_ok2 (@LG RL) = true }.

Section WithFP.
  Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RDATA : RelocData RLOC} {RIMG : RelocImg RLOC}
          {RRW : RelocRW RLOC RDATA} {RPF : RelocPF RLOC} {RENV : RelocLeptEnvOL RLOC}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 LG).
Proof.
ltac2:(KReplay.run1 (kr_t_LeptStderr ()) ["WithFP"] "p;1p;2p;:g0000j12Tg0016j21Tg002El:0Tp,2fxp,4RLOCR0p,5RCODEp,6RSITESp,5RDATAp,4RIMGp,3RRWp,3RPF%20p,4RENV,10M:0o"). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 LG).
Proof.
ltac2:(KReplay.run1 (kr_t_LeptStderr ()) ["WithFP"] "p;1p;2p;:g0000j12Tg003Tj21Tg004cl:0Tp,2fxp,4RLOCR0p,5RCODEp,6RSITESp,5RDATAp,4RIMGp,3RRWp,3RPF%20p,4RENV,10M:0o"). Qed.
End WithFP.
