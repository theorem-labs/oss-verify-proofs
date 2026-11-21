(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the larger auxiliary vector and its CONFIG_RSEQ entries; the start-up hand-off tables computed in the build). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.Riscv Require Import Instr.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit CertRefl.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanChain A_PlanImage A_Atable A_HooksDefs A_HS_000 PlanCoGen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

(* A_plan_000's fresh-variable literals are shifted by +5 from the recorded text:
   105, 239, 251, 269, 270, 271 for 100, 234, 246, 264, 265, 266 (fifteen occurrences,
   six distinct, every one inside [escale 4096 (EVar n)]; the plan carries no [EVar]
   literal below 14, so no [V_*] variable can be touched).  Each value was READ OFF the
   failing state, not fitted: the collector was run stage by stage and each stage took
   its literal from the previous stage's [nxt - 1], pinned a second time by the map
   ledger's [am_base := EMd M_MUL (ELit 4096) (EVar 105)] with [am_len := ELit 65536]
   matching the [PShDisj]'s own [ELit 65536]
   (two probe builds).  The shift is [NX0]'s
   14 -> 15 (the auxv's new [V_GID]) less the one [LMiss] read that
   [auxw 18 9 (ELit (a_entry A))] removes at pair 18, which the aux copy loop reads
   before any of them.  A uniform sweep of d in {12..16} failed at every stage, so +5 is
   measured and not a fitted guess. *)

(* THE LITERALS ARE NOT r-DEPENDENT ANY MORE, AND THE OFFSET IS WHY [A_plan_of] STAYS.
   They were, for one revision.  [init_kn_tail] (AsanPlanCore.v) claims two extra auxv
   pairs at r = 1, and while their VALUE words were [KUnk] the walk read each as an
   unknown and allocated a fresh variable, so every variable the r = 1 build allocated
   afterwards was two higher than the r = 0 build's: at this level's hand-off,
   nxt 288 / |kn| 1141 against nxt 290 / |kn| 1145 (a probe build).  The
   fifteen occurrences below were fitted to the r = 0 run, so at r = 1 the level stopped
   with [CErr 3] at a [PShDisj], pc 1922936, nxt 108, |kn| 225, in a state whose only
   CONSTRAINED [EVar] indices were 0..14, 52, 69 and 107 -- none of the six literals, and
   [nxt - 1 = 107] (two probe builds, agreeing).
   Shifting the fifteen by [2 * r] did move r = 1 to [PHandoff 0] at the r = 0 pc
   (that build), but it could never CLOSE this level: the shifted build arrives in its own
   numbering, [entails0] (AsanPlanCore.v:4185-4197) compares registers and maps for
   syntactic equality, and [PlanCoGen.pc_meet] weakens only the knowledge list, so one
   hand-off table cannot be entailed by two differently-numbered arrivals however many
   rounds [pc_go] runs -- which is exactly what a later probe build reported, as
   a red r = 0 certificate (the collector falls back to the recorded [A_HS_000]).

   The repair is one layer up, in [init_kn_tail]: the two CONFIG_RSEQ value words are now
   claimed with the model's own literals ([StackLayout.auxv_entries] emits 28 and 32 at
   LPS 75d69e0079f9), so nothing is read as unknown, no fresh variable is allocated, and
   the two builds share ONE numbering again.  [A_plan_000] therefore serves both, which is
   what [A_Chain] needs: both flag arms run this one plan.  Their arrivals still differ in
   the auxv tail, so each build keeps its own hand-off table (below).
   [A_plan_of] is kept, applied at 0, because the offset is a real property of this plan:
   the fifteen literals are a function of how many fresh variables the launch has spent
   before this level's first [PShDisj], and that number is the thing a future auxv change
   moves.  It is the parameter the next revision reads, not dead generality. *)
(* [A_plan_of] has exactly ONE instantiation today, [A_plan_000 := A_plan_of 0], and one
   reference in the 2,767-file unit (that line).  It is kept parameterised because the
   offset has already moved twice -- +5 for [NX0]'s new [V_GID], then +2 which the
   [init_kn_tail] repair removes -- so [d] is where the next auxv change is read, not
   dead generality.  Do not delete it on a count; re-measure the offset instead. *)
Definition A_plan_of (d : nat) : plan := PRun [] (PX XIMemset [] (PRun [] (PX XEnvScan [] (PRun [] (PX XPnScan [] (PRun [] (PX XIMemcpy [] (PRun [] (PSys YSetTid (PRun [] (PX XIMemcpy [] (PRun [0x51ad30] (PJoinX (ELit 0) 0xbc3f30 8 (PRun [] (PExt 50 [] (PRun [] (PMmap PSpin (PRun [] (PMmap PSpin (PRun [] (PMmap PSpin (PRun [0x1d52b8] (PX XIStrncpy [] (PRun [0x1d52b8] (PX XIStrncpy [] (PDropRange (ELit 0x6fd600) (ELit 0xfff) (PDropRange (ELit 0x6fc600) (ELit 0xfff) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar (105 + d))) (ELit 65536) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar (105 + d))) (ELit 65536) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PX XIMemset [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemset [] (PRun [] (PX XIMemcpy [] (PRun [] (PX XIMemcpy [] (PRun [0x1ca5fc] (PDropRange (escale 4096 (EVar (105 + d))) (ELit 0x10000) (PRun [] (PExt 50 [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar (239 + d))) (ELit 3727360) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar (239 + d))) (ELit 3727360) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1c1248] (PExt 67 [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar (251 + d))) (ELit 137439023104) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar (251 + d))) (ELit 137439023104) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1de8a8] (PFresh 9 12 None (PRun [] (PMmapIn PSpin (PRun [0x1c45a8] (PDiamondT 0x1c47d4 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar (269 + d))) (ELit 8388608) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar (269 + d))) (ELit 8388608) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PShDisj (escale 4096 (EVar (270 + d))) (ELit 4096) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar (270 + d))) (ELit 4096) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [] (PMmap PSpin (PBand 0 (PShDisj (escale 4096 (EVar (271 + d))) (ELit 65536) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar (271 + d))) (ELit 65536) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1c45a8] (PDiamondT 0x1c47d4 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PHandoff 0))))))) (PShDisj (escale 4096 (EVar (271 + d))) (ELit 65536) (ELit 65536) (ELit 12279808) (PShDisj (escale 4096 (EVar (271 + d))) (ELit 65536) (eaddz e_pgsp (-8388608)) (ELit 12582912) (PRun [0x1c45a8] (PDiamondT 0x1c47d4 4 [5; 6; 7; 11; 14; 15; 16; 17; 28]%nat (PRun [] (PX XMemset [] (PHandoff 0)))))))))))))))))))))) PSpin))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
Definition A_plan_000 : plan := A_plan_of 0.
Definition A_ranges_000 : list (Z * nat) := [(0x199a10, 23%nat); (0x199b6c, 19%nat); (0x199d18, 85%nat); (0x19c37c, 28%nat); (0x19c488, 49%nat); (0x19c5cc, 44%nat); (0x19c6c0, 23%nat); (0x1a0990, 13%nat); (0x1a0a44, 10%nat); (0x1a0f48, 32%nat); (0x1a1010, 12%nat); (0x1a76cc, 879%nat); (0x1a84cc, 16%nat); (0x1a8550, 51%nat); (0x1b7674, 85%nat); (0x1b8568, 6626%nat); (0x1c1240, 91%nat); (0x1c1910, 6%nat); (0x1c2364, 19%nat); (0x1c2430, 24%nat); (0x1c2654, 21%nat); (0x1c2788, 26%nat); (0x1c2c44, 25%nat); (0x1c2e6c, 25%nat); (0x1c2fa4, 13%nat); (0x1c3aa4, 5%nat); (0x1c4524, 52%nat); (0x1c46a8, 9%nat); (0x1c4778, 35%nat); (0x1c48b0, 18%nat); (0x1c5634, 20%nat); (0x1c56b4, 11%nat); (0x1c9900, 10%nat); (0x1ca098, 29%nat); (0x1ca55c, 131%nat); (0x1caa7c, 57%nat); (0x1cacec, 6%nat); (0x1cb0a0, 108%nat); (0x1cb280, 39%nat); (0x1cb508, 16%nat); (0x1cb588, 8%nat); (0x1cc1dc, 18%nat); (0x1ccc98, 89%nat); (0x1cd0bc, 12%nat); (0x1cdb84, 16%nat); (0x1ceddc, 43%nat); (0x1ceee8, 7%nat); (0x1cf6c8, 74%nat); (0x1cf820, 41%nat); (0x1d0ec4, 7%nat); (0x1d1568, 30%nat); (0x1d1824, 40%nat); (0x1d1c78, 5%nat); (0x1d1cc0, 5%nat); (0x1d1f88, 46%nat); (0x1d216c, 14%nat); (0x1d27c4, 93%nat); (0x1d2c70, 1206%nat); (0x1d43ec, 64%nat); (0x1d4578, 72%nat); (0x1d46fc, 21%nat); (0x1d47e4, 88%nat); (0x1d4ac8, 44%nat); (0x1d4e08, 13%nat); (0x1d4e84, 28%nat); (0x1d4ff4, 21%nat); (0x1d523c, 14%nat); (0x1d52b0, 32%nat); (0x1d5748, 15%nat); (0x1d5a30, 25%nat); (0x1d657c, 77%nat); (0x1d69c4, 27%nat); (0x1d6be8, 6%nat); (0x1d6e3c, 64%nat); (0x1d7488, 71%nat); (0x1d7b28, 21%nat); (0x1d7c78, 14%nat); (0x1d82ec, 7%nat); (0x1dc5a8, 73%nat); (0x1dc72c, 6%nat); (0x1dc910, 11%nat); (0x1ddf20, 26%nat); (0x1de12c, 7%nat); (0x1de848, 37%nat); (0x1df044, 5%nat); (0x1df8f8, 5%nat); (0x1dfbc4, 5%nat); (0x1e0120, 10%nat); (0x1e017c, 7%nat); (0x1e0218, 6%nat); (0x1e03b0, 42%nat); (0x1e04b4, 9%nat); (0x1e0ad4, 46%nat); (0x1e0d20, 8%nat); (0x1e2540, 21%nat); (0x1ecab8, 265%nat); (0x1ef978, 7%nat); (0x1f2a0c, 98%nat); (0x1f303c, 7%nat); (0x51a2a8, 28%nat); (0x51a34c, 25%nat); (0x51a4b4, 7%nat); (0x51a624, 84%nat); (0x51a840, 66%nat); (0x51aa28, 202%nat); (0x51af40, 53%nat); (0x52690c, 66%nat); (0x5272a0, 7%nat); (0x527498, 5%nat); (0x527528, 7%nat); (0x529430, 11%nat); (0x52959c, 57%nat); (0x52a358, 29%nat); (0x52a3fc, 18%nat); (0x52a4f8, 23%nat); (0x52a5b8, 7%nat)].
Definition A_IT_000 : itab := mk_itab_ranges A_SEGS A_ranges_000.
Lemma A_IT_000_ok : itab_sound A_SEGS A_IT_000.
Proof. apply APS.mk_itab_ranges_sound. Qed.
Definition A_shape_000 : shape := SHole 0.

(* ONE HAND-OFF TABLE PER KERNEL BUILD.  [init_acs_of] takes the run's CONFIG_RSEQ flag
   [r] since the auxv tail became [r]-parametric ([AsanPlanCore.init_kn_tail]), and
   [Run.valid_input] leaves the kernel build free, so this level must close at r = 0 and
   at r = 1 over the SAME plan.  Each build's table is COMPUTED from its own arrival,
   never written: [PlanCoGen.pc_collect] records the state arriving at [PHandoff 0]
   ([CErr 4]) or meets it with the table so far ([CErr 3]), and a table it returns with
   [COk] is one the check accepts; the two certificates below re-check them, and
   [pc_next]'s fallback is the recorded [A_HS_000], which they would then reject, so a
   failed collection cannot pass as a success.
   ONE table for both builds, met over the two arrivals, is not enough at LPS 727298f3:
   the tail's CONFIG_RSEQ pair and AT_NULL sit at different pairs under the two builds,
   so the meet drops every claim on pairs 26-28, and level 1's [getauxval] walk, which
   reads keys past pair 25 for an item the vector does not hold, stops at the unclaimed
   key of pair 26.  So level 1 starts from each build's own table (A_G_001.v). *)
Definition A_chk_000 (r : Z) (T : nat -> option acs) : cres :=
  check A_SEGS A_IT_000 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 T 0%nat 400000%nat 40000%nat None (init_acs_of r A_T) A_plan_000.
Definition A_HSg_000_r0 : acs := Eval vm_compute in pc_next (pc_collect (A_chk_000 0)) A_HS_000.
Definition A_HSg_000_r1 : acs := Eval vm_compute in pc_next (pc_collect (A_chk_000 1)) A_HS_000.

Lemma A_cert_000_r0 :
  check A_SEGS A_IT_000 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_000_r0) 0%nat 400000%nat 40000%nat None (init_acs_of 0 A_T) A_plan_000
  = COk A_shape_000.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_000)). Qed.

Lemma A_cert_000_r1 :
  check A_SEGS A_IT_000 A_T NX0 AsanInit.LIMIT A_XN0 A_XE0 A_XB0 (HS_one A_HSg_000_r1) 0%nat 400000%nat 40000%nat None (init_acs_of 1 A_T) A_plan_000
  = COk A_shape_000.
Proof. ltac2:(cert_refl_vm constr:(COk A_shape_000)). Qed.
