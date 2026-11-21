(* SPDX-License-Identifier: MIT *)
(* The ASan build's start-up hand-off states at LPS 727298f3, computed in the build (the method of
   jsoncons/fuzz_bigint's PlanRegenK.v and double-conversion/string_to_double_fuzzer's PlanRegen.v, over this
   unit's plan and state types), and the variable renumbering the recorded start-up plans are checked under.

   The renumbering [FSH] is read off the runs, never chosen: from the design-1 start state ([BsImages.hinit_r],
   NX0 14) the start-up plan reaches its hand-off 90 with every fresh variable at +5; the plan after it names
   old 263 where the run has 268 (+5) and old 326 where the run has 333 (+7).  With that map every start-up
   plan checks at both CONFIG_RSEQ values.

   [BsStartupHS1] .. [BsStartupHSF] compute their tables with [collect]: rerun the check, add each hand-off
   the table lacks (code 4), and weaken each one the run does not imply (code 3) to what both imply
   ([join_states]).  Each CONFIG_RSEQ start state has its own tables up to hand-offs 100 .. 105 (the plans
   there read the knowledge the two values' states differ in); the main entry's table [BsStartupHSF] is
   one, met from both.  SOUNDNESS DOES NOT REST ON ANY OF THIS: every certificate
   ([BsStartupCertG1] .. [G10]) re-runs the check against the computed tables; a wrong map or table can only
   make a certificate fail. *)
From Stdlib Require Import ZArith List Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BxSymExec3 BothPlanCore BothPlan BsHSTab
  BsImages BsPlanImages BsStartupPlan BsPlanRegen.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition FSH (v : nat) : nat := if Nat.ltb v 11 then v else if Nat.ltb v 326 then (v + 5)%nat else (v + 7)%nat.

Definition hlookup (m : list (nat * acs)) (h : nat) : option acs := hs_lookup h m.
Fixpoint hupd (h : nat) (c : acs) (m : list (nat * acs)) : list (nat * acs) :=
  match m with [] => [(h, c)] | (k, d) :: r => if Nat.eqb h k then (h, c) :: r else (k, d) :: hupd h c r end.

(** the first state, with only the facts both list, the looser bounds and the larger counter *)
Definition join_states (a b : acs) : acs :=
  let ss := a_ss a in
  let kn' := List.filter (fun K => existsb (kentry_eqb K) (kn b)) (kn a) in
  ACS (SSR (s_pc ss) (s_regs ss) (s_log ss) kn' (Nat.max (s_next ss) (s_next (a_ss b))) (s_resv ss))
      (a_maps a) (Z.max (a_totsz a) (a_totsz b)) (Z.min (a_ylo a) (a_ylo b)) (Z.max (a_eager a) (a_eager b))
      (a_vis a) (a_ghost a) (Z.max (a_abytes a) (a_abytes b)) (a_brk a) (a_fd a) (a_tidset a) (a_vmops a).

Fixpoint collect (fuel : nat) (run : (nat -> option acs) -> cres) (m : list (nat * acs)) : list (nat * acs) :=
  match fuel with
  | O => m
  | S f =>
      match run (hlookup m) with
      | CErr code (PHandoff h) cs =>
          if Z.eqb code 4 then collect f run (hupd h cs m)
          else if Z.eqb code 3 then
            match hlookup m h with Some a => collect f run (hupd h (join_states a cs) m) | None => m end
          else m
      | _ => m
      end
  end.

(** the state a table holds at [h] (only ever read at a key the table has) *)
Definition hst (m : list (nat * acs)) (h : nat) : acs := match hlookup m h with Some a => a | None => hinit_r 0 end.

Definition RXN (id : nat) (args : list expr) (cs : acs) : option acs := None.
Definition RXE (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition RXB (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

(** the check every start-up certificate runs, on the renumbered plan *)
Definition su_check (IT : list (Z * nat)) (js : nat -> option acs) (cs : acs) (p : plan) : cres :=
  check ASEGS (mk_itab_ranges ASEGS IT) ASAN_H NX0 HLIMIT RXN RXE RXB js CERT_KC0 CERT_BFUEL CERT_FUEL None cs (psh FSH p).

(** a table for the plans [ps] (ranges, plan, start state), filled and weakened until each plan's check runs through *)
Definition regen (fuel : nat) (ps : list (list (Z * nat) * plan * acs)) : list (nat * acs) :=
  fold_left (fun m '(IT, p, cs) => collect fuel (fun js => su_check IT js cs p) m) ps [].
