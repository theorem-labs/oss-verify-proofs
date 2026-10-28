(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2PFBase V2PFSpec.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_V2LeptStderr () := "K47Corelib4Init5Logic2eq01C5ARocqVerifyHarness?AgentSubmission2V28V2PFSpec6ls_ok1I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c5ARocqVerifyHarness?AgentSubmission2V2<V2LeptStderr3L16C5ARocqVerifyHarness?AgentSubmission2V28V2PFSpec6ls_ok2C5ARocqVerifyHarness?AgentSubmission2V28V2PFSpecGlept_stderr_s1_contractc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptStderr7L21_ok1C5ARocqVerifyHarness?AgentSubmission2V28V2PFSpecGlept_stderr_s2_contractc5ARocqVerifyHarness?AgentSubmission2V2<V2LeptStderr7L21_ok2".
Import ListNotations.
Open Scope Z_scope.

Definition L16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x17e28; SSP.ls_handler_cell := 0x45f10; SSP.ls_devnull := 0x17df0;
     SSP.ls_canary_got := 0x44ec8; SSP.ls_canary := 0x764d8;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x44000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x77000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x103da; 0x105f0; 0x1062f; 0x10e9c; 0x11030; 0x1117f; 0x1129a; 0x112c8;
                  0x113f5; 0x115a1; 0x11706; 0x1184f; 0x11b78; 0x11e98; 0x12007; 0x1210c; 0x12207; 0x10f13; 0x10f60];
     SSP.ls_fmts2 := [0x1240e];
     SSP.ls_sev_got := 0x44e98; SSP.ls_sev := 0x45f08 |}.

Lemma L21_ok1 : ls_ok1 L16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptStderr ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Aj30Tg001[R0g002;R1'2g002[#1=001do"). Qed.
Lemma L21_ok2 : ls_ok2 L16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptStderr ()) [] "p;2p;1p;3g0000j22Tg003Sj11Tg001Aj30Tg001[R0g002;R1'2g002[#1=001do"). Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L16).
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptStderr ()) ["WithFP"] "p;3g004Jj30Tp,2fxg002[g005R30o"). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L16).
Proof.
ltac2:(KReplay.run1 (kr_t_V2LeptStderr ()) ["WithFP"] "p;3g006Nj30Tp,2fxg002[g007V30o"). Qed.
End WithFP.
