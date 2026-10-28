(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Export RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RunDraw () := "C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z6to_natC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leK47Corelib4Init5Logic2eq01C56Stdlib6ZArith4Znat5Z2Nat2idK47Corelib4Init6Specif3sig01K47Corelib7Numbers7BinNums8positive02I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic3and00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C47Corelib4Init6Specif9proj2_sigc5ARocqVerifyHarness?AgentSubmission5Ubsan7RunDraw>pstage_len_sig".
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac atop_facts :=
  lazymatch goal with
  | _ : (0x7fff7f800000 <= @ATOP _ <= 0x7FFFFF800000)%Z |- _ => idtac
  | |- context [@ATOP _] => pose proof atop_range as ATOPR
  | _ : context [@ATOP _] |- _ => pose proof atop_range as ATOPR
  | _ => idtac
  end.
Ltac sec_facts :=
  lazymatch goal with
  | _ : (0 <= @SECRET _ < 2^64)%Z |- _ => idtac
  | _ => pose proof sec_range as SECR
  end.

(* [comment removed for export] *)
Definition pstage_len_sig : { n : nat | Z.of_nat n = 65536 }.
Proof.
ltac2:(KReplay.run1 (kr_t_RunDraw ()) [] "h01nh11mh21Hp;1p;3p;2p;4g0000j1;Tg000Pj19Tg000nj32Tg001Hj1:Tg001hj24Tg002Ej21Tg002aj28Tg003Aj27Tg003[j26Tg0049j45Tg004Uj13Tf0R0#3#3p=0g005:R1g005YR2%;0g0067#0#0#0#0#0#0#0#0#9R332X01%:3g006\g0077R1f1R4/40g007WR532f2R6/14[R711401464=215R8[f3/16\81840P4n2001000000120000000X12X02P7^12^02P0g0087P31715O3b2,63C5o"). Qed.
Definition PSTAGE_LEN : nat := proj1_sig pstage_len_sig.
Lemma PSTAGE_LEN_Z : Z.of_nat PSTAGE_LEN = 65536.
Proof.
ltac2:(KReplay.run1 (kr_t_RunDraw ()) [] "h01np;1p;3g0000j15Tg000Pj13Tg000nj32Tg008Uj34Tg004Uj11Tf0R0#1#1p=0g005:R1g005Y%50g0067#0#0#0#0#0#0#0#0#332X01g009534o"). Qed.
Ltac stage_facts :=
  lazymatch goal with
  | _ : Z.of_nat PSTAGE_LEN = 65536 |- _ => idtac
  | |- context [PSTAGE_LEN] => pose proof PSTAGE_LEN_Z as PSTAGER
  | _ : context [PSTAGE_LEN] |- _ => pose proof PSTAGE_LEN_Z as PSTAGER
  | _ => idtac
  end.
Ltac lia := atop_facts; stage_facts; Stdlib.micromega.Lia.lia.
Ltac nia := atop_facts; stage_facts; Stdlib.micromega.Lia.nia.
