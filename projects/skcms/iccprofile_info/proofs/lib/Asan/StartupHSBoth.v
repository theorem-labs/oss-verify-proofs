(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the recorded hand-off state HS0 is gone: the hand-off and join states are computed in the build, once per CONFIG_RSEQ layout, by PlanRegen.collect_hj over the start-up check, the plan's fresh variables are renumbered where it is checked (vsh_su), and its stack window is 6144513 bytes, was 8388608. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AsanPlanCore AsanPlan AsanPlanFO AsanInit
  BothAsanPlanImages StartHooksBoth StartupPlanBoth PlanRegen.
Import ListNotations. Import AX2. Import APC. Import AP.
Open Scope Z_scope.

Definition KC0 : nat := 0.
Definition BFUEL : nat := 400000.
Definition FUEL : nat := 3000.
Definition IT0 : itab := mk_itab_ranges ASEGS startup_plan_ranges.

(** The start-up plan's fresh variables, renumbered where the plan is checked.  The launch has
    three more slots ([AsanInit.V_VDSO], [V_MSS], [V_GID]: the first fresh variable is [NX_HW] = 13,
    not 10) and reads more of the auxv, so the run allocates its fresh variables at other numbers
    than the run the recorded plan was written against.  The map is read from builds that
    stop the plan where it names a variable:
    below 10 unchanged, 10..333
    shifted by 4, 334 and above by 5.  A wrong map can only make the certificate below red. *)
Definition vsh_su (v : nat) : nat := if Nat.ltb v 10 then v else if Nat.ltb v 334 then (v + 4)%nat else (v + 5)%nat.

(** The plan at layout [r] with [w] in front of its hand-off ([pre_ho]), its join state read from
    [J], or the recorded one renumbered as the collector's seed. *)
Definition startup_plan_w (w : plan -> plan) (J : nat -> option acs) : plan :=
  pre_ho w (psh vsh_su (startup_plan_of (match J 1%nat with Some js => js | None => ash vsh_su startup_js1 end))).
Definition su_run_w (r : Z) (w : plan -> plan) (H J : nat -> option acs) : cres :=
  APF.check ASEGS IT0 (INFO_BOTH_at r) NX0 AsanInit.LIMIT (XNS r) XE0 XB0 H KC0 BFUEL FUEL None (init_acs_hw (INFO_BOTH_at r))
    (startup_plan_w w J).

(** What the start-up hands off, made blob-free.  At LPS 727298f3 the launch's sixteen AT_RANDOM
    bytes are a known blob ([AsanInit]'s [KBlob] at [e_atrandom]), so the run hands off that
    block and the canary it copies from it as blob bytes: byte 0 at 6269360 and bytes 2..7 at
    6269362; the main forest is checked against
    a blob-free hand-off state ([acs_noblob]).  The recorded hand-off state held the canary as
    one 8-byte word whose value was the start-up variable the thread's copy at 6138208 also held.
    Before the hand-off the plan therefore
    - gives the canary an 8-byte word with a fresh value ([PWordFresh]) and removes the two blob
      pieces ([PWordFresh] then [PHavocWords] on a piece's address renames the first word there
      and drops the later ones; [PForget [0]] drops the renamed copy just put in front), the
      word itself getting a fresh value in that step;
    - drops the thread's copy ([PDropRange]) and renames the word's variable to the variable that
      copy held ([PRename]), so the canary is again one start-up variable and the hand-off
      counter, which numbers the main plans' variables, is what the run without the weakening
      leaves;
    - drops the AT_RANDOM block ([PDropRange]).
    The run without the weakening ([SUP]) supplies the copy's variable and the counter.  The run
    then checks the weakened state, so the weakening only forgets. *)
Definition SUP_1 : list (nat * acs) * list (nat * acs) := Eval vm_compute in collect_hj 40 (su_run_w 1 (fun k => k)) [] [] [].
Definition SUP_0 : list (nat * acs) * list (nat * acs) := Eval vm_compute in collect_hj 40 (su_run_w 0 (fun k => k)) [] [] [].
Definition sup_ho (r : Z) : acs :=
  match hlookup (fst (if Z.eqb r 1 then SUP_1 else SUP_0)) 0%nat with Some a => a | None => init_acs_hw (INFO_BOTH_at r) end.
Definition tls_var (r : Z) : nat :=
  match find (fun K => match K with KWord (SA (ELit 0) k) 8%nat (EVar _) => Z.eqb k 6138208 | _ => false end) (kn (sup_ho r)) with
  | Some (KWord _ _ (EVar u)) => u
  | _ => 0%nat
  end.
Definition su_weaken (r : Z) (k : plan) : plan :=
  PWordFresh (ELit 6269360) 8 (PWordFresh (ELit 6269362) 6 (PHavocWords [ELit 6269362] (PForget [0%nat]
    (PHavocWords [ELit 6269360] (PDropRange (ELit 6138208) (ELit 8)
      (PRename [((nxt (sup_ho r) + 3)%nat, tls_var r)] (PDropRange (e_atrandom (INFO_BOTH_at r)) (ELit 16) k))))))).

(** The start-up plan at layout [r] with join map [J], and its check with hand-off map [H]. *)
Definition startup_plan_k (r : Z) (J : nat -> option acs) : plan := startup_plan_w (su_weaken r) J.
Definition su_run (r : Z) (H J : nat -> option acs) : cres := su_run_w r (su_weaken r) H J.

(** The hand-off and join states, computed by the collector from empty maps, once per layout.
    [StartupCertBoth] re-checks the plan against them. *)
Definition SU_1 : list (nat * acs) * list (nat * acs) := Eval vm_compute in collect_hj 40 (su_run 1) [] [] [].
Definition SU_0 : list (nat * acs) * list (nat * acs) := Eval vm_compute in collect_hj 40 (su_run 0) [] [] [].
Definition SU (rsb : bool) : list (nat * acs) * list (nat * acs) := if rsb then SU_1 else SU_0.

Definition HS_both (rsb : bool) : nat -> option acs := hlookup (fst (SU rsb)).
Definition JS_both (rsb : bool) : nat -> option acs := hlookup (snd (SU rsb)).
Definition startup_plan (rsb : bool) : plan := startup_plan_k (rseq_z rsb) (JS_both rsb).
