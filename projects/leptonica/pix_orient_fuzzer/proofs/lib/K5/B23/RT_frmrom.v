(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA FrmRun.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_frmrom () := "K47Corelib4Init5Logic2eq01C69OSSVerify5KrLib2K53B236FrmRun:rom_frm_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma asegs_frm : rom_frm_ok asegs = true.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_frmrom ()) [] "p;2p;1p;3g0000j22Tg000Jj11Tg001Gj30Tg001aR0g002AR1'2g002a#1=001do"). Qed.
