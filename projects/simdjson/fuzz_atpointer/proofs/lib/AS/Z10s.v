(* SPDX-License-Identifier: MIT *)
(* Theorem Labs, 2026-11: image B's start-up join and hand-off states, per value [r] of the run's
   CONFIG_RSEQ flag (0 or 1), computed from the run by [PlanRegen.regen] in place of the recorded
   ones, which were written against the released model's launch; image B's twin of AS/Z10q.v.
   The recorded plan [Z10h.startup_plan] is checked renumbered ([PlanRegen.pshd]), with these
   join states put in. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z2z Z2y Z3h Z10h PlanRegen.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* the certificate's own check ([Z7d.startup_cert]'s arguments), at flag [r], from state [cs]
   under loop context [lc] *)
Definition chk_from_B (r : Z) (HS : nat -> option acs) (lc : option loopctx) (cs : acs) (p : plan) : cres :=
  check AsanUbsan.M.loaded_segments (mk_itab_ranges AsanUbsan.M.loaded_segments startup_plan_ranges) ASAN_B NX0
        target_alloc_limit r (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) HS
        0%nat 400000%nat 3000%nat lc cs p.

(* The plan's variables at each compaction depth, renumbered to the new run (step maps; see
   notes/probe-simdjson__fuzz_atpointer.md, row P11, for the probe line each value is read from).
   Depth 0: the launch has [V_GID] at 11, so every fresh variable is one higher; two more fresh
   variables come after the run's auxv scan (old 29 on: +3), and two more after old 358 (+5).
   Depth 1 and below: the first compaction's targets start at [NX0] (11 -> 12), +1. *)
Definition F_B : list (list (nat * nat)) :=
  [[(11, 1); (29, 3); (358, 5)]%nat; [(11, 1)]%nat; [(11, 1)]%nat; [(11, 1)]%nat].

Definition plan_B (VJ : list (nat * acs)) : plan := pshd F_B (hlookup VJ) 0 startup_plan.
Definition run_B (r : Z) (VJ HL : list (nat * acs)) : cres :=
  chk_from_B r (hlookup HL) None (asan_b_init r) (plan_B VJ).
Definition arms_B (r : Z) (HL : list (nat * acs)) (j : nat) (js : acs) (lo : nat) (cs : acs) (ka : plan) : cres :=
  chk_from_B r (hlookup HL) (Some (JC j js SNil (nxt cs) lo)) cs ka.
Definition REGEN_B (r : Z) : list (nat * acs) * list (nat * acs) * cres :=
  regen 30 (run_B r) (arms_B r) [] [].
