(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YN06 YQ0b.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 YI00 YI02
UI1i YP14 YI08 YI0c UI3h UI4v.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition PC_M1 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0xb0).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable API : AllocAPI ubs2_msyms.
Local Notation segs := ubs2segs.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Definition at_M1 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model) : Prop :=
rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac memc mdc /\
rgba_regs regs0 regs1 /\
getr regs1 26 = Z_to_bv 64 cfp /\ getr regs1 8 = Z_to_bv 64 r /\ getr regs1 10 = Z_to_bv 64 W /\ getr regs1 11 = Z_to_bv 64 H /\
slot regs0 memc 144 0 /\ slot regs0 memc 152 0 /\
rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur memc /\ cgif_at memc g s /\
Permutation (blocks Lc Ac) (BASE r g N img fmt rest s bef beffmt).
Definition K_M1 : Prop := forall regs1 Lc Ac memc mdc,
at_M1 regs1 Lc Ac memc mdc ->
SR segs (cfg_at regs1 PC_M1 memc mdc) (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
End b.
End a.
