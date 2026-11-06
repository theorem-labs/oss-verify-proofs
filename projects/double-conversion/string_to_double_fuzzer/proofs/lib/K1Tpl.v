(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AsanPlan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition HEADPC : Z := 0xa4174.
Definition RPPC : Z := 0x77fe8.
Definition C100 (k : plan) : plan := PRun [RPPC] (PExt 100 [] k).
Definition rfirst (k : plan) : plan := PRun [] (PExt 12 [] (C100 (C100 (C100 (PRun [] (PX XMemcpy [] (PRun [HEADPC] k))))))).
Definition rbody : plan := rfirst PNext.
Definition AFTER_READS : Z := 0xa41e0.
Definition RQC : Z := 0x62b84.
Definition QCS : Z := 0x75a2c.
Definition QCD : Z := 0x75a74.

Definition HOFF0 : list nat := [5; 6; 7; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition HOFF : list nat := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.
Definition LENX (q r : nat) : expr := EAlu ALU_ADD (EMd M_MUL (ELit 65536) (EVar q)) (EVar r).
Definition fin (q r B : nat) (K : plan) : plan := PRun [AFTER_READS] (PRespell 19 (LENX q r) (PBump B (PHavoc HOFF K))).
Definition hcut (K : plan) : plan := PRun [HEADPC] (PHavoc HOFF0 K).

Definition rd_full (jz : Z) (k : plan) : plan := PRun [] (PExt 11 [ELit jz] (C100 (C100 (C100 (PRun [] (PX XMemcpy [] k)))))).
Definition cp_short (k : plan) : plan :=
  PRun [RQC] (PExt 101 [] (PRun [QCS] (PExt 102 [] (PRun [QCD] (PExt 103 [] (PRun [] (PX XMemcpy [] k))))))).
Definition cp_long (k : plan) : plan := C100 (C100 (C100 (PRun [] (PX XMemcpy [] k)))).
Definition eof (q r B : nat) (K : plan) : plan := PRun [] (PExt 13 [] (fin q r B K)).

Definition R1 (K : plan) : plan := PExt 18 [] (rd_full 1 (hcut K)).

Definition rarms (jz : Z) (q r B : nat) (K : plan) : plan :=
  PCase2 (EVar r) 0 (PRun [] (PExt 11 [ELit jz] (fin q r B K)))
    (PCase2 (EVar r) 64 (PRun [] (PExt 11 [ELit jz] (cp_short (eof q r B K))))
                        (PRun [] (PExt 11 [ELit jz] (cp_long (eof q r B K))))).

Definition F1 (q r B : nat) (K : plan) : plan :=
  PExt 18 [] (PCase2 (EVar q) 1 (PExt 24 [] (rarms 1 q r B K)) PContra).

Fixpoint fulls (jz : Z) (m : nat) (k : plan) : plan :=
  match m with O => k | S m' => rd_full jz (fulls (jz + 1) m' k) end.
Definition farm (q0 : Z) (m : nat) (q r B : nat) (K : plan) : plan := PExt 24 [] (fulls q0 m (rarms (q0 + Z.of_nat m) q r B K)).
Fixpoint fcases (q0 : Z) (m n : nat) (q r B : nat) (K : plan) : plan :=
  match n with
  | O => PContra
  | S n' => PCase2 (EVar q) (q0 + Z.of_nat m) (farm q0 m q r B K) (fcases q0 (S m) n' q r B K)
  end.
Definition Fj (j : nat) (q r B : nat) (K : plan) : plan :=
  let q0 := 2 ^ (Z.of_nat j - 1) in
  PExt 18 [] (PCase2 (EVar q) (q0 - 1) PContra (fcases q0 0 (Z.to_nat q0) q r B K)).

Definition Ri (i : nat) (K : plan) : plan :=
  let h := Z.to_nat (2 ^ (Z.of_nat i - 1)) in PExt 18 [] (fulls (Z.of_nat h) h (hcut K)).


Definition hcut0 (K : plan) : plan := PHavoc HOFF0 K.
Definition RiL (i : nat) (J : nat) (INV : acs) (K : plan) : plan :=
  PExt 18 [] (rfirst (PLoop J (ELit (2 ^ (Z.of_nat i - 1) - 1)) INV rbody (hcut0 K))).
Definition fpre (j : nat) (q : nat) (k : plan) : plan :=
  let q0 := 2 ^ (Z.of_nat j - 1) in
  PExt 18 [] (PCase2 (EVar q) (q0 - 1) PContra (PCase2 (EVar q) (2 * q0 - 1) (PExt 24 [] (PCase2 (EVar q) q0 (PHandoff 990) k)) PContra)).
Definition fpre2 (j : nat) (q : nat) (k : plan) : plan :=
  let q0 := 2 ^ (Z.of_nat j - 1) in fpre j q (PCase2 (EVar q) (q0 + 1) (PHandoff 990) k).
Definition tails (q r B : nat) (K : plan) : plan :=
  PRun [] (PExt 17 [] (PCase2 (EVar r) 0 (fin q r B K)
     (PCase2 (EVar r) 64 (cp_short (eof q r B K)) (cp_long (eof q r B K))))).
Definition FjL (j : nat) (q r B : nat) (K : plan) (J : nat) (INV : acs) : plan :=
  let q0 := 2 ^ (Z.of_nat j - 1) in let qm := 2 ^ Z.of_nat j - 2 in
  PExt 18 [] (PCase2 (EVar q) (q0 - 1) PContra (PCase2 (EVar q) (2 * q0 - 1)
    (PExt 24 [] (PCase2 (EVar q) q0 (tails q r B K)
       (rfirst (PLoop J (esub (EVar q) (ELit (q0 + 1))) INV rbody (PCase2 (EVar q) qm (tails q r B K) (tails q r B K))))))
    PContra)).

Definition HRPC : Z := 0xa41b8.
Definition rbodyH : plan := PRun [] (PExt 12 [] (C100 (C100 (C100 (PRun [] (PX XMemcpy [] (PRun [HRPC] PNext))))))).
Definition fpreH (j : nat) (q : nat) (k : plan) : plan :=
  let q0 := 2 ^ (Z.of_nat j - 1) in
  PExt 18 [] (PCase2 (EVar q) (q0 - 1) PContra (PCase2 (EVar q) (2 * q0 - 1) (PExt 24 [] k) PContra)).
Definition rprobeH0 : plan := PHandoff 991.
Definition rprobeH1 : plan := PRun [] (PExt 12 [] (C100 (C100 (C100 (PRun [] (PX XMemcpy [] (PRun [HRPC] (PHandoff 992)))))))).
Definition rprobeHB : plan := PRun [] (PExt 12 [] (C100 (C100 (C100 (PRun [] (PX XMemcpy [] (PRun [HRPC] (PHandoff 993)))))))).
Definition eof2 (qm : Z) (q r B : nat) (K : plan) : plan := PCase2 (EVar q) qm (eof q r B K) (eof q r B K).
Definition tails2 (qm : Z) (q r B : nat) (K : plan) : plan :=
  PRun [] (PExt 17 [] (PCase2 (EVar r) 0 (fin q r B K)
     (PCase2 (EVar r) 64 (cp_short (eof2 qm q r B K)) (cp_long (eof2 qm q r B K))))).
Definition FjH (j : nat) (q r B : nat) (K : plan) (J : nat) (INV : acs) : plan :=
  let q0 := 2 ^ (Z.of_nat j - 1) in let qm := 2 ^ Z.of_nat j - 2 in
  fpreH j q (PLoop J (esub (EVar q) (ELit q0)) INV rbodyH (tails2 qm q r B K)).
