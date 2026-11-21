(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the recorded hand-off states are replaced by the join and hand-off states computed in the build per CONFIG_RSEQ flag by PlanRegen's collectors over the start-up check, the hand-off states collected in one run of the check, with the plan's fresh variables renumbered by maps read from probe runs). *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0m4 X0li X0lh X0ly X0lj X0kj X0lv X0n6 X0n4 PlanRegen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition BFUEL : nat := 400000.
Definition KC0 : nat := 0.
Definition FUEL : nat := 3000.
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges.

(** The recorded plan's fresh variables, renumbered where the plan is checked ([PlanRegen.psh]).
    The launch has two more variables ([V_G] 10, [V_GID] 11: [NX0] is 12, not 10) and reads more of
    the auxv, so the run's variables sit higher than the recorded plan's.  The plan compacts its
    variables at [PRename]s; [vsh0] is the map up to the first rename, [vsh1] the map after it.
    Both are read from the probe runs of the plan at LPS 727298f3 (probe 2 in
    notes/probe-speex__speex_decode_fuzzer_float.md: pairs (77, 81) and (357, 363) at both flags in
    both builds; at the first rename the state's fresh variables are the rename's sources under
    [vsh0]; after it the shift is NX0's 2). *)
Definition vsh0 (v : nat) : nat :=
  if Nat.ltb v 10 then v else if Nat.ltb v 357 then (v + 4)%nat else (v + 6)%nat.
Definition vsh1 (v : nat) : nat := if Nat.ltb v 10 then v else (v + 2)%nat.
Definition su_P : plan := psh [vsh0; vsh1] startup_plan.

(** The start-up check at CONFIG_RSEQ flag [r], hand-off map [H], plan [p]. *)
Definition su_check (r : Z) (H : nat -> option acs) (p : plan) : cres :=
  check ASEGS IT0 ASAN_A NX0 X0kj.LIMIT r XN0 XE0 XB0 H KC0 BFUEL FUEL None (asan_a_init r) p.

(** The join states of the plan's two [PVia]s (ids 0 and 3), collected from the recorded ones
    renumbered by [vsh1] as seeds, then the hand-off states reached from them, once per flag.
    [X0lx] checks the plan against them. *)
Definition su_seed : list (nat * acs) := [(0%nat, ash vsh1 js_0); (3%nat, ash vsh1 js_3)].
Definition JS_0 : list (nat * acs) := Eval vm_compute in
  collect_js ASAN_A 12 (fun J => su_check 0 (HJ J) (pjs_arms J su_P)) su_seed [].
Definition JS_1 : list (nat * acs) := Eval vm_compute in
  collect_js ASAN_A 12 (fun J => su_check 1 (HJ J) (pjs_arms J su_P)) su_seed [].
Definition su_plan (r : Z) : plan := pjs (hlookup (if Z.eqb r 1 then JS_1 else JS_0)) su_P.
(** The same check run once per flag by [check_coll] (lib/AS/X0lh.v), giving each hand-off it
    reaches to PlanRegen's [hvisit], from [bm] (the collector's fuel left and its hand-off map):
    [RUN_r]'s map is the map [collect_handoffs] makes in one run per state it adds, and its
    answer's shape is the start-up's shape that AS/X0lxR0.v and X0lxR1.v certify with [check]. *)
Definition su_coll (r : Z) (p : plan) (bm : nat * list (nat * acs)) : cres * (nat * list (nat * acs)) :=
  check_coll ASEGS IT0 ASAN_A NX0 X0kj.LIMIT r XN0 XE0 XB0 KC0 BFUEL _ hvisit FUEL None (asan_a_init r) p bm.
Definition RUN_0 : cres * (nat * list (nat * acs)) := Eval vm_compute in su_coll 0 (su_plan 0) (12%nat, []).
Definition RUN_1 : cres * (nat * list (nat * acs)) := Eval vm_compute in su_coll 1 (su_plan 1) (12%nat, []).
Definition HL_0 : list (nat * acs) := Eval vm_compute in coll_map RUN_0.
Definition HL_1 : list (nat * acs) := Eval vm_compute in coll_map RUN_1.
Definition HS_asan (r : Z) (h : nat) : option acs :=
  if Z.eqb r 0 then hlookup HL_0 h else if Z.eqb r 1 then hlookup HL_1 h else None.
