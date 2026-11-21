(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the larger auxiliary vector and its CONFIG_RSEQ entries; the start-up hand-off tables computed in the build). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain B_PlanImage B_Atable B_HooksDefs B_HS_000 PlanCoGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* B_plan_000's fresh-variable literals are shifted by +5 from the recorded text:
   105, 239, 251, 269, 270, 271 for 100, 234, 246, 264, 265, 266 (fifteen occurrences,
   six distinct, every one inside [escale 4096 (EVar n)]; the plan carries no [EVar]
   literal below 14, so no [V_*] variable can be touched).  Measured on B, not inferred
   from the A twin: each literal was read off its own failing state, stage by stage,
   in a probe build whose last stage reaches [PHandoff 0] at
   pc 0x1CA74C with [pc_collect] returning [COk].  The shift is [NX0]'s 14 -> 15 (the
   auxv's new [V_GID]) less the one [LMiss] read that [auxw 18 9 (ELit (a_entry A))]
   removes at pair 18, which the aux copy loop reads before any of them. *)

(* THE LITERALS ARE NOT r-DEPENDENT ANY MORE, AND THE OFFSET IS WHY [B_plan_of] STAYS.
   They were, for one revision.  [init_kn_tail] (AsanPlanCore.v) claims two extra auxv
   pairs at r = 1, and while their VALUE words were [KUnk] the walk read each as an
   unknown and allocated a fresh variable, so every variable the r = 1 build allocated
   afterwards was two higher than the r = 0 build's: at this level's hand-off,
   nxt 288 / |kn| 1141 against nxt 290 / |kn| 1145 (a probe build of the A
   twin; B carries the same six literals with the same multiplicities, 3+2+2+2+2+4 = 15).
   The fifteen occurrences below were fitted to the r = 0 run, so at r = 1 the level
   stopped with [CErr 3] at a [PShDisj] in a state none of the six literals carried a
   fact in (two probe builds).  Shifting the
   fifteen by [2 * r] did move r = 1 to [PHandoff 0] at the r = 0 pc (that A build), but it
   could never CLOSE this level: the shifted build arrives in its own numbering,
   [entails0] (AsanPlanCore.v:4185-4197) compares registers and maps for syntactic
   equality, and [PlanCoGen.pc_meet] weakens only the knowledge list, so one hand-off
   table cannot be entailed by two differently-numbered arrivals however many rounds
   [pc_go] runs -- which is what a later probe build reported, as a red r = 0
   certificate (the collector falls back to the recorded [B_HS_000]).

   The repair is one layer up, in [init_kn_tail]: the two CONFIG_RSEQ value words are now
   claimed with the model's own literals ([StackLayout.auxv_entries] emits 28 and 32 at
   LPS 75d69e0079f9), so nothing is read as unknown, no fresh variable is allocated, and
   the two builds share ONE numbering again.  [B_plan_000] therefore serves both, which is
   what [B_Chain] needs: both flag arms run this one plan.  Their arrivals still differ in
   the auxv tail, so each build keeps its own hand-off table (below).
   [B_plan_of] is kept, applied at 0, because the offset is a real property of this plan:
   the fifteen literals are a function of how many fresh variables the launch has spent
   before this level's first [PShDisj], and that number is what a future auxv change
   moves.  It is the parameter the next revision reads, not dead generality. *)
(* [B_plan_of] has exactly ONE instantiation today, [B_plan_000 := B_plan_of 0], and one
   reference in the 2,767-file unit (that line).  It is kept parameterised because the
   offset has already moved twice -- +5 for [NX0]'s new [V_GID], then +2 which the
   [init_kn_tail] repair removes -- so [d] is where the next auxv change is read, not
   dead generality.  Do not delete it on a count; re-measure the offset instead. *)
Definition B_plan_of (d : nat) : plan := PRun [] (PX XIMemset [] (PRun [] (PX XEnvScan [] (PRun [] (PX XPnScan [] (PRun [] (PX XIMemcpy [] (PRun [] (PSys YSetTid (PRun [] (PX XIMemcpy [] (PRun [0x55342c] (PJoinX (ELit 0) 0xbf6730 8 (PRun [] (PExt 50 [] (PRun [] (PMmap PSpin (PRun [] (PMmap PSpin (PRun [] (PMmap PSpin (PRun [0x1d0270] (PX XIStrncpy [] (PRun [0x1d0270] (PX XIStrncpy [] (PDropRange (ELit 0x72fe00) (ELit 0xfff) (PDropRange (ELit 0x72ee00) (ELit 0xfff) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar (105 + d))) (ELit 65536) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar (105 + d))) (ELit 65536) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemset [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemset [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [0x1c55b4] (PDropRange (escale 4096 (EVar (105 + d))) (ELit 0x10000) (PRun [] (PExt 50 [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar (239 + d))) (ELit 3727360) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar (239 + d))) (ELit 3727360) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1bc200] (PExt 67 [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar (251 + d))) (ELit 137439023104) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar (251 + d))) (ELit 137439023104) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1d9860] (PFresh 9 12 None (PRun [] (PMmapIn PSpin (PRun [0x1bf560] (PDiamondT 0x1bf78c 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar (269 + d))) (ELit 8388608) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar (269 + d))) (ELit 8388608) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar (270 + d))) (ELit 4096) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar (270 + d))) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PBand 0 (PShDisj (escale 4096 (EVar (271 + d))) (ELit 65536) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar (271 + d))) (ELit 65536) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1bf560] (PDiamondT 0x1bf78c 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PHandoff 0))))))) (PShDisj (escale 4096 (EVar (271 + d))) (ELit 65536) (ELit 65536) (ELit 12484608) (PShDisj (escale 4096 (EVar (271 + d))) (ELit 65536) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1bf560] (PDiamondT 0x1bf78c 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PHandoff 0)))))))))))))))))))))) PSpin))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition B_plan_000 : plan := B_plan_of 0.
Definition B_ranges_000 : list (Z * nat) := [(0x1949c8, 23%nat); (0x194b24, 19%nat); (0x194cd0, 85%nat); (0x197334, 28%nat); (0x197440, 49%nat); (0x197584, 44%nat); (0x197678, 23%nat); (0x19b948, 13%nat); (0x19b9fc, 10%nat); (0x19bf00, 32%nat); (0x19bfc8, 12%nat); (0x1a2684, 879%nat); (0x1a3484, 16%nat); (0x1a3508, 51%nat); (0x1b262c, 85%nat); (0x1b3520, 6626%nat); (0x1bc1f8, 91%nat); (0x1bc8c8, 6%nat); (0x1bd31c, 19%nat); (0x1bd3e8, 24%nat); (0x1bd60c, 21%nat); (0x1bd740, 26%nat); (0x1bdbfc, 25%nat); (0x1bde24, 25%nat); (0x1bdf5c, 13%nat); (0x1bea5c, 5%nat); (0x1bf4dc, 52%nat); (0x1bf660, 9%nat); (0x1bf730, 35%nat); (0x1bf868, 18%nat); (0x1c05ec, 20%nat); (0x1c066c, 11%nat); (0x1c48b8, 10%nat); (0x1c5050, 29%nat); (0x1c5514, 131%nat); (0x1c5a34, 57%nat); (0x1c5ca4, 6%nat); (0x1c6058, 108%nat); (0x1c6238, 39%nat); (0x1c64c0, 16%nat); (0x1c6540, 8%nat); (0x1c7194, 18%nat); (0x1c7c50, 89%nat); (0x1c8074, 12%nat); (0x1c8b3c, 16%nat); (0x1c9d94, 43%nat); (0x1c9ea0, 7%nat); (0x1ca680, 74%nat); (0x1ca7d8, 41%nat); (0x1cbe7c, 7%nat); (0x1cc520, 30%nat); (0x1cc7dc, 40%nat); (0x1ccc30, 5%nat); (0x1ccc78, 5%nat); (0x1ccf40, 46%nat); (0x1cd124, 14%nat); (0x1cd77c, 93%nat); (0x1cdc28, 1206%nat); (0x1cf3a4, 64%nat); (0x1cf530, 72%nat); (0x1cf6b4, 21%nat); (0x1cf79c, 88%nat); (0x1cfa80, 44%nat); (0x1cfdc0, 13%nat); (0x1cfe3c, 28%nat); (0x1cffac, 21%nat); (0x1d01f4, 14%nat); (0x1d0268, 32%nat); (0x1d0700, 15%nat); (0x1d09e8, 25%nat); (0x1d1534, 77%nat); (0x1d197c, 27%nat); (0x1d1ba0, 6%nat); (0x1d1df4, 64%nat); (0x1d2440, 71%nat); (0x1d2ae0, 21%nat); (0x1d2c30, 14%nat); (0x1d32a4, 7%nat); (0x1d7560, 73%nat); (0x1d76e4, 6%nat); (0x1d78c8, 11%nat); (0x1d8ed8, 26%nat); (0x1d90e4, 7%nat); (0x1d9800, 37%nat); (0x1d9ffc, 5%nat); (0x1da8b0, 5%nat); (0x1dab7c, 5%nat); (0x1db0d8, 10%nat); (0x1db134, 7%nat); (0x1db1d0, 6%nat); (0x1db368, 42%nat); (0x1db46c, 9%nat); (0x1dba8c, 46%nat); (0x1dbcd8, 8%nat); (0x1dd4f8, 21%nat); (0x1e7a70, 265%nat); (0x1ea930, 7%nat); (0x1ed9c4, 98%nat); (0x1edff4, 7%nat); (0x5529a4, 28%nat); (0x552a48, 25%nat); (0x552bb0, 7%nat); (0x552d20, 84%nat); (0x552f3c, 66%nat); (0x553124, 202%nat); (0x55363c, 53%nat); (0x55f008, 66%nat); (0x55f99c, 7%nat); (0x55fb94, 5%nat); (0x55fc24, 7%nat); (0x561b2c, 11%nat); (0x561c98, 57%nat); (0x562a54, 29%nat); (0x562af8, 18%nat); (0x562bf4, 23%nat); (0x562cb4, 7%nat)].
Definition B_IT_000 : itab := mk_itab_ranges B_SEGS B_ranges_000.
Lemma B_IT_000_ok : itab_sound B_SEGS B_IT_000.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition B_shape_000 : shape := SHole 0.

(* ONE HAND-OFF TABLE PER KERNEL BUILD; see the A twin's note for the argument.  Each
   build's table is collected from its own arrival, and the two certificates below
   re-check them.  Level 1 starts from each build's own table (B_G_001.v). *)
Definition B_chk_000 (r : Z) (T : nat -> option acs) : cres :=
  check B_SEGS B_IT_000 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 T 0%nat 400000%nat 40000%nat None (init_acs_of r B_T) B_plan_000.
Definition B_HSg_000_r0 : acs := Eval vm_compute in pc_next (pc_collect (B_chk_000 0)) B_HS_000.
Definition B_HSg_000_r1 : acs := Eval vm_compute in pc_next (pc_collect (B_chk_000 1)) B_HS_000.

Lemma B_cert_000_r0 :
  check B_SEGS B_IT_000 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_000_r0) 0%nat 400000%nat 40000%nat None (init_acs_of 0 B_T) B_plan_000
  = COk B_shape_000.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_000)). Qed.

Lemma B_cert_000_r1 :
  check B_SEGS B_IT_000 B_T NX0 AsanInit.LIMIT B_XN0 B_XE0 B_XB0 (HS_one B_HSg_000_r1) 0%nat 400000%nat 40000%nat None (init_acs_of 1 B_T) B_plan_000
  = COk B_shape_000.
Proof. ltac2:(cert_refl_vm constr:(COk B_shape_000)). Qed.
