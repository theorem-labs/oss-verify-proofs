(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumSpecs PFLib PFSpecLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23PFBase O23PFSpec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_O23LeptStderr () := "K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib3O239O23PFSpec6ls_ok1C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c59OSSVerify5KrLib3O23=O23LeptStderr3L16C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O239O23PFSpec6ls_ok2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O239O23PFSpecGlept_stderr_s1_contractC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23LeptStderr7L21_ok1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3O239O23PFSpecGlept_stderr_s2_contractC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3O23=O23LeptStderr7L21_ok2C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Definition L16 : SSP.ls_addrs :=
  {| SSP.ls_entry := 0x63080; SSP.ls_handler_cell := 0x1137c0; SSP.ls_devnull := 0x63048;
     SSP.ls_canary_got := 0x112758; SSP.ls_canary := 0x143f90;
     SSP.ls_img_lo := 0x10000; SSP.ls_img_hi := 0x10f000;
     SSP.ls_frame := 3376; SSP.ls_sp_lo := 0x145000 + 3376; SSP.ls_sp_hi := 0x800000000000;
     SSP.ls_fmts1 := [0x109df; 0x11fa6; 0x11fe5; 0x152bb; 0x15a6a; 0x161d5; 0x1695b; 0x16989;
                  0x176df; 0x17e92; 0x18b5e; 0x192de; 0x1ac83; 0x1c04f; 0x1c811; 0x1d009; 0x1d4d1];
     SSP.ls_fmts2 := [0x1e325];
     SSP.ls_sev_got := 0x1125c8; SSP.ls_sev := 0x1137b8 |}.

Lemma L21_ok1 : ls_ok1 L16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptStderr ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Cj30Tg001]R0g002=R1'2g002]#1=001do"). Qed.
Lemma L21_ok2 : ls_ok2 L16 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptStderr ()) [] "p;2p;1p;3g0000j22Tg003Wj11Tg001Cj30Tg001]R0g002=R1'2g002]#1=001do"). Qed.

Section WithFP.
Context {fx : FPState}.
Theorem lept_stderr_s1 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s1 L16).
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptStderr ()) ["WithFP"] "p;3g004Pj30Tp,2fxg002]g005Z30o"). Qed.
Theorem lept_stderr_s2 : SSP.sum_contract SEGS (SSP.spec_lept_stderr_s2 L16).
Proof.
ltac2:(KReplay.run1 (kr_t_O23LeptStderr ()) ["WithFP"] "p;3g006Xj30Tp,2fxg002]g007b30o"). Qed.
End WithFP.
