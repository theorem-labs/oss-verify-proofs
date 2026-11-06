(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2PFBase O2PFSpec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_O2LeptStderr () := "K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib2O28O2PFSpec6ls_ok1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib2O2<O2LeptStderr3L16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2PFSpec6ls_ok2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2PFSpecGlept_stderr_s1_contractC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2LeptStderr7L21_ok1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2O28O2PFSpecGlept_stderr_s2_contractC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib2O2<O2LeptStderr7L21_ok2C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Definition L16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x17bd8; SSP.ls_handler_cell := 0x394e8; SSP.ls_devnull := 0x17ba0;
     SSP.ls_canary_got := 0x384a0; SSP.ls_canary := 0x69aa8;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x38000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x6b000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x103da; 0x105e3; 0x10622; 0x10e7e; 0x11012; 0x11161; 0x1127c; 0x112aa;
                  0x113d7; 0x11583; 0x116e8; 0x11831; 0x11b5a; 0x11e7a; 0x11fe9; 0x120ee; 0x121e9; 0x10ef5; 0x10f42];
     SSP.ls_fmts2 := [0x123f0];
     SSP.ls_sev_got := 0x38470; SSP.ls_sev := 0x394e0 |}.

Lemma L21_ok1 : ls_ok1 L16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2LeptStderr ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Aj30Tg001[R0g002;R1'2g002[#1=001do"). Qed.
Lemma L21_ok2 : ls_ok2 L16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O2LeptStderr ()) [] "p;2p;1p;3g0000j22Tg003Sj11Tg001Aj30Tg001[R0g002;R1'2g002[#1=001do"). Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L16).
Proof.
ltac2:(KReplay.run1 (kr_t_O2LeptStderr ()) ["WithFP"] "p;3g004Jj30Tp,2fxg002[g005R30o"). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L16).
Proof.
ltac2:(KReplay.run1 (kr_t_O2LeptStderr ()) ["WithFP"] "p;3g006Nj30Tp,2fxg002[g007V30o"). Qed.
End WithFP.
