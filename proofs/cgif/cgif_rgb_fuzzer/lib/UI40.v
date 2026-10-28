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
Definition PC_M2 : Z := Eval vm_compute in (ubs2_A_cgif_rgb_addframe + 0x208).
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable API : AllocAPI ubs2_msyms.
Local Notation segs := ubs2segs.
Variables (L : layout) (A : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model).
Variables (r cfp g wfn ctx path attr gen loops W H bef beffmt cur : Z) (s : cgif_st) (N : Z).
Variables (img fmt fattr fgen delay : Z) (rest : list (Z * Z)).
Definition at_M2 (regs1 : bvmap 5 word) (Lc : layout) (Ac : astate) (memc : word -> option byte) (mdc : Model)
(pnew fimg : Z) (imgl : list Z) (c f h u p x : Z) : Prop :=
rgba_inv API L A regs0 mem0 md0 r cfp g W H bef beffmt s N img fmt fattr fgen delay rest Lc Ac memc mdc /\
rgba_regs regs0 regs1 /\ (fmt = 3 \/ fmt = 4) /\ 1 <= N /\
getr regs1 8 = Z_to_bv 64 r /\ getr regs1 26 = Z_to_bv 64 cfp /\ getr regs1 18 = Z_to_bv 64 pnew /\
getr regs1 9 = Z_to_bv 64 fimg /\ getr regs1 21 = Z_to_bv 64 2 /\ getr regs1 27 = Z_to_bv 64 N /\
slot regs0 memc 112 fmt /\ slot regs0 memc 120 img /\
getr regs1 20 = Z_to_bv 64 c /\ getr regs1 10 = Z_to_bv 64 x /\
fcfg_at regs0 fattr delay memc fimg 0 0 /\ rgb_obj r g wfn ctx path attr gen loops W H bef beffmt cur memc /\
cgif_at memc g s /\ img_at N img fmt memc imgl /\ pnew <> 0 /\ fimg <> 0 /\
c <> 0 /\ c mod 16 = 0 /\ 0 <= f < 2 ^ 64 /\ 0 <= h < 2 ^ 64 /\ 0 <= u < 2 ^ 64 /\ 0 <= p < 2 ^ 64 /\ 0 <= x < 2 ^ 64 /\
obj_at segs memc c LAY_Cht [f; h; u; p; 0; 0; TS0] /\
Permutation (blocks Lc Ac) (BASE r g N img fmt rest s bef beffmt ++ [(pnew, fmt * N); (fimg, N); (c, CHT_SIZE)] ++
optb f (4 * TS0) ++ optb h (3 * TS0) ++ optb u TS0 ++ optb p (3 * TS0) ++ optb x (4 * TS0)).
Definition K_M2 : Prop := forall regs1 Lc Ac memc mdc pnew fimg imgl c f h u p x,
at_M2 regs1 Lc Ac memc mdc pnew fimg imgl c f h u p x ->
SR segs (cfg_at regs1 PC_M2 memc mdc) (rgba_post API L A regs0 mem0 md0 r g wfn ctx path attr gen loops W H bef beffmt s N img fmt rest).
End b.
End a.
