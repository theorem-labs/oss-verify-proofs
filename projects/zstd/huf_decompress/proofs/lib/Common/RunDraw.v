(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require Export StackLayout.   (* [comment removed for export] *)
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Export RunConst.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RunDraw () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib3Lib8RunConst7ATOP_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8RunConst7ATOP_hiC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01I59OSSVerify5KrLib3Lib8RunConst9runConstT00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib3Lib8RunConst:SECRET_rngC1?~~~~~~~~~~~~~~~".
Open Scope Z_scope.

Lemma atop_range {rc : runConstT} : 0x7fff7f800000 <= ATOP <= 0x7FFFFF800000.
Proof.
ltac2:(KReplay.run1 (kr_t_RunDraw ()) [] "h02rcp;1p;2p;4g0000j10Tg000Uj16Tg0013j1;Tg001ij24Tg002Ej11Tg002jj18Tg003cj19Tg004\j4:Tf0R0#1#1p=<%10#1#1#1p=2%00#0p=5%00#0#0#0p=7%00#0#0#0#0#0#0#0p=3g0057R1g0064#<#2#2#2R2#0#2#2#0#5#7#3#3#6%;0R3'4%12#2#2#0#5#7#3#3#6,43%80%90C:X01P0O1W0o"). Qed.
Lemma sec_range {rc : runConstT} : 0 <= SECRET < 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_RunDraw ()) [] "h02rcp;1g006Yj10Tg0057R0f0R1#0X00P1O1W0o"). Qed.

(* [comment removed for export] *)
Ltac atop_facts :=
  lazymatch goal with
  | _ : 0x7fff7f800000 <= @ATOP _ <= 0x7FFFFF800000 |- _ => idtac
  | |- context [@ATOP _] => pose proof atop_range
  | _ : context [@ATOP _] |- _ => pose proof atop_range
  | _ => idtac
  end.
Ltac sec_facts :=
  lazymatch goal with
  | _ : 0 <= @SECRET _ < 2^64 |- _ => idtac
  | _ => pose proof sec_range
  end.

(* [comment removed for export] *)
Ltac lia := atop_facts; Stdlib.micromega.Lia.lia.
Ltac nia := atop_facts; Stdlib.micromega.Lia.nia.
