(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SX2.

Definition lit_sr_0 : list expr := [ELit 0; ELit 80724; EAlu ALU_ADD (EVar 0) (ELit (-128)); ELit 67584; ELit 223152; EVar 14; EVar 15; EVar 16; EAlu ALU_ADD (EVar 2) (ELit 2); EVar 2; EAlu ALU_ADD (EVar 2) (ELit 2); EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EExt true 0 1 (EVar 7))) (ELit 49)) (EExt false 0 1 (EVar 6)); EAlu ALU_ADD (EAlu ALU_ADD (EVar 2) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EExt true 0 1 (EVar 7))) (ELit 49)) (EExt false 0 1 (EVar 6)))) (ELit 6); EAlu ALU_ADD (EAlu ALU_ADD (EVar 3) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EExt true 0 1 (EVar 7))) (ELit 49)) (EExt false 0 1 (EVar 6))))) (ELit (-6)); EVar 44; EVar 24; EVar 25; EVar 26; EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EExt true 0 1 (EVar 7))) (ELit 49)) (EExt false 0 1 (EVar 6)); EAlu ALU_ADD (EAlu ALU_ADD (EVar 2) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EExt true 0 1 (EVar 7))) (ELit 49)) (EExt false 0 1 (EVar 6)))) (ELit 6); EAlu ALU_ADD (EAlu ALU_ADD (EVar 3) (EMd M_MUL (ELit (-1)) (EAlu ALU_OR (EAlu ALU_SRL (EMd M_MUL (ELit 144115188075855872) (EExt true 0 1 (EVar 7))) (ELit 49)) (EExt false 0 1 (EVar 6))))) (ELit (-6)); EExt true 0 1 (EVar 7); ELit 157321; EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40].
Definition LITS_SR : list (list expr) := [lit_sr_0].
Definition lit_lg_0 : list sentry := [].
Definition LITS_LG : list (list sentry) := [lit_lg_0].
Definition lit_kn_0 : list kentry := [KRange (EVar 2) 360448 140737479966720; KRange (EVar 3) 65536 67108863; KWord {| a_base := EVar 2; a_off := 0 |} 1 (EVar 6); KWord {| a_base := EVar 2; a_off := 1 |} 1 (EVar 7); KRange (EVar 6) 0 255; KRange (EVar 7) 0 255].
Definition LITS_KN : list (list kentry) := [lit_kn_0].
