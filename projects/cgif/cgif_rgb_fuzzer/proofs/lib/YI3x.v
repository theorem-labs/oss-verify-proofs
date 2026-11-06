(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YN06 YQ0b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YH04 YH07 YH06 YI00 YI02
YI1i YP14 YI08 YI0c YI3h YI4v.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition PC_M1 : Z := 0x1348c.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable API : AllocAPI src2_msyms.
Local Notation segs := src2segs.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Definition at_M1 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model) : Prop :=
rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac memc mdc /\
rgba_regs regs0 regs1 /\
getr regs1 19 = Z_to_bv 64 cfp /\ getr regs1 8 = Z_to_bv 64 r /\ getr regs1 10 = Z_to_bv 64 W /\ getr regs1 11 = Z_to_bv 64 H /\
slot regs0 memc 136 0 /\ slot regs0 memc 144 0 /\
rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur memc /\ cgif_at memc g s /\
Permutation (blocks Lc Ac) (BASE r g N img fmt rest s bef beffmt).
Definition K_M1 : Prop := forall regs1 Lc Ac memc mdc,
at_M1 regs1 Lc Ac memc mdc ->
SR segs (cfg_at regs1 PC_M1 memc mdc) (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
End b.
End a.
