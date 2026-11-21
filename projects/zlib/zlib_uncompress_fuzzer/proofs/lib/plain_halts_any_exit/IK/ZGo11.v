(* THE STURDY DRIVER, EDITION 2 (edition 1, , stays as it ran).
   It adds NO rule and NO theorem: every step it takes is one of the walk kit's own proved one-instruction rules
   (IK/ZStep.v, IK/ZMem.v), applied by the kit's own tactics (IK/ZTac.v `zstep_with`, `zbr_with`, `zret_with`;
   IK/ITac.v `tstep_with`, `zsmall`). What it removes from a walk proof: the NUMBER of step calls of a stretch
   and the DIRECTION written at each branch.
   WHAT EDITION 2 CHANGES (round 1's red and the non-author read):
   - the user forms are Tactic Notations: the continuation's application is handed over UNRUN (edition 1 ran
     it at the call, before the first step);
   - a run takes AT LEAST ONE instruction; the run of no instruction is a form of its own name (`zuntil0`);
   - a run FAILS when a step fails in its middle, and when its fuel ends: no silent stop;
   - the driver prints nothing.
   FORMS:
   - `zuntil fd (tac)`: at least one instruction, then on until `tac` applies (give it the application of the
     next join point's continuation: it applies only at that join point's label). `zuntil0`: `tac` may apply
     at once. `zuntil_n fd (tac) n`: the same as `zuntil` with the fuel n.
   - `zgo fd stop`: at least one instruction, then on until the pc is `stop`. `zgo_n fd stop n`: with fuel n.
   - `zfd_c`: a LOOKUP WITH NO TABLE: the three facts of a pc by computation from the image's segments named
     in the goal.
   THE NUMERAL 400 below is the FUEL of a run (the most instructions one run may take).
   EDITION 3 (rounds 1 and 2 were red for this): THE TACTIC HANDED TO `zuntil` MUST NOT BE A BARE CALL OF AN
   Ltac WHOSE BODY IS A MATCH ON THE GOAL: Ltac runs such a call where it is written as an argument, before the
   run's first step, and its failure ends the run. Start that Ltac's body with `idtac;` (the control text's
   `kapp` does), or hand over a plain tactic (`eapply ..`). ONE CHANGE IN THE DRIVER's CODE: `zgo_k` picks the
   kit's tactic BY THE DECODED KIND (a branch: the kit's branch tactic, either way; a register jump: the kit's
   step, else the kit's return; any other: the kit's step). Edition 2 tried them in a row, and the kit's branch
   tactic leaves such a row at once on a text that is no branch, so the return was never reached. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require Import TSet ZStep ZMem ZTac ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require Import ZArr ZArr4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* the lookup with no table *)
Ltac zfd_c pc k :=
  lazymatch goal with
  | |- realizes ?sg (zcfg _ _ _ _ _) _ =>
      let fw := eval vm_compute in (fetch_word sg (w64 pc)) in
      lazymatch fw with
      | Some ?w =>
          let e := eval vm_compute in (is_ecall w) in
          let d := eval vm_compute in (decode_any w) in
          let F := fresh "Fc" in
          let E := fresh "Ec" in
          let D := fresh "Dc" in
          assert (F : fetch_word sg (w64 pc) = Some w) by (vm_compute; reflexivity);
          assert (E : is_ecall w = e) by (vm_compute; reflexivity);
          assert (D : decode_any w = d) by (vm_compute; reflexivity);
          k F E D; clear F E D
      | _ => fail 1 "zfd_c: the image holds no word at this pc"
      end
  end.

(* EDITION 4: a value that holds no variable is made a numeral (the kit's `zlit` does this where the hand
   text asks for it; the driver does it wherever the newest register value is closed, and nowhere else) *)
(* A NOTE ON ITS COST (the reader's D6): `zlit_closed` closes "numeral = value" by `reflexivity`: the checker
   compares the two again at the lemma's end; that is nothing for arithmetic on numerals and would be dear for a
   closed value that reads the image's data (the kit's `zlit` has the same cost where the hand text calls it). *)
Ltac zclosed e :=
  match e with
  | context [?x] => is_var x; fail 1 "zclosed: the value holds a variable"
  | _ => idtac
  end.

Ltac zlit_closed :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ =>
      lazymatch e with
      | Z0 => fail "a numeral already"
      | Zpos _ => fail "a numeral already"
      | Zneg _ => fail "a numeral already"
      | _ => zclosed e; let v := eval vm_compute in e in zsetreg v ltac:(reflexivity)
      end
  end.

(* one instruction, whatever its kind *)
(* EDITION 8: ONE FAILURE WORD A CAUSE. Each way the driver itself refuses has a word of its own, in capitals,
   first in its message: STURDY-PC-NOT-NUMERAL, STURDY-OPEN-BRANCH, STURDY-NO-STEP, STURDY-FUEL-CONT,
   STURDY-FUEL-LABEL, STURDY-FUEL-BRANCH, STURDY-FIRST-OPEN-BRANCH. The run's loop no longer hides an inner
   failure behind "no applicable tactic" (it tries the handed-in tactic with `tryif`, not inside `first`). *)
(* EDITION 9 (the non-author reader's ask on the open-branch form): WHAT "OPEN" MEANS. A branch is OPEN when
   the kit's branch rule applies with EVERY PREMISE BUT THE CONDITION closed, and the condition is proved
   neither way. A branch whose rule fails on another premise (the word fact, the not-halted fact) is NOT open:
   that is a failure with a word of its own (STURDY-BRANCH-PREMISE), never a stop. `zbr_premises` is the kit's
   branch rule with its condition and its continuation left open. *)
Ltac zbr_premises F E D :=
  eapply (zu_branch_b true); [ zexact F | zexact E | zexact D | zhalted | | ].

(* EDITION 13 (two converters' measures; nothing else of edition 12 is changed; the module's name stays `ZGo11`).
   (a) THE CHEAP TRY AT A TEST. Measured on heavy texts: a run pays seconds for each FAILING try of the kit's
       condition tactic (its arithmetic tries every separation case of a large context): a test that is not
       taken, tried "taken" first; the tries at an open test. `zcond_cheap` is the kit's condition tactic word
       for word with ONE change: every arithmetic call is the kit's PLAIN solver (`lia_std`: no separation
       cases). `zbr_cheap` is the kit's branch tactic with that condition tactic. A test is now tried: cheap
       taken, cheap not taken, then the kit's own tactic both ways as before. The cheap try can only DECIDE: it
       proves the condition's truth value as the kit's rule asks it; where it proves neither way, edition 12's
       tries follow unchanged, so an open test and a branch premise that is not closed give the same words.
   (b) THE ZERO TERM AFTER A TABLE LOAD. The kit's address reader leaves "index - 0" in a loaded table value,
       and the model's facts are said at the plain index, so the next test stayed open. `zdrop0`: where the
       newest register value holds a "- 0" or "+ 0" term, the term is rewritten away in the newest value only
       (the form is tested first; nothing else is touched). It is tried after every instruction that is no
       branch, before the small-value and closed-value words. *)
(* EDITION 14, FOURTH FILE (a diagnosis that gave ONE unprovable range goal of a heavy context to each solver apart:
   the kit's FIRST TIER gave up in 0.09 s; the kit's relevance solver, its core solver, the plain fast solver and
   `lia` each ran over 45 s without an answer). SO THE DRIVER's CHEAP WORD IS THE KIT's FIRST TIER, everywhere a
   cheap try stands: at a test (edition 13 used the plain fast solver there), in the small-value word, and for the
   index bound of the cheap pass at a load. Where the first tier proves nothing the kit's own words run as before
   (at a test and at a load); the small-value word has no second try: a value that the first tier does not show
   small stays wrapped (a text that needs more calls the kit's own small-value word where it needs it). *)
Ltac zgo_t1 := solve [ OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK.ZPrune.zlia_t1 ].

Ltac zcond_cheap :=
  cbv beta iota delta [zcond];
  repeat match goal with H : ?x mod 18446744073709551616 = _ |- context [?x mod 18446744073709551616] => rewrite H end;
  rewrite ?mod_small_u64 by zgo_t1;
  rewrite ?swrap64_small by zgo_t1; rewrite ?swrap32_small by zgo_t1;
  first [ reflexivity | zcond_cheap_decide ]
with zcond_cheap_decide :=
  lazymatch goal with
  | |- (_ =? _) = true => apply Z.eqb_eq; zgo_t1
  | |- (_ =? _) = false => apply Z.eqb_neq; zgo_t1
  | |- (_ <? _) = true => apply Z.ltb_lt; zgo_t1
  | |- (_ <? _) = false => apply Z.ltb_ge; zgo_t1
  | |- negb _ = true => apply Bool.negb_true_iff; zcond_cheap_decide
  | |- negb _ = false => apply Bool.negb_false_iff; zcond_cheap_decide
  | |- _ => zgo_t1
  end.

Ltac zbr_cheap bv F E D :=
  lazymatch type of D with
  | decode_any _ = Some (Branch _ _ _ _, _) =>
      eapply (zu_branch_b bv); [ zexact F | zexact E | zexact D | zhalted | znorm; zcond_cheap | ]; zcbv_iota; znorm
  | _ => fail "STURDY-CHEAP-NO-BRANCH: the instruction at this pc is no branch"
  end.

(* the four tries at a test, cheapest first *)
Ltac zbr_any F E D :=
  first [ zbr_cheap true F E D | zbr_cheap false F E D | zbr_with true F E D | zbr_with false F E D ].

Ltac zdrop0 :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ =>
      lazymatch e with
      | context [_ - 0] => idtac
      | context [_ + 0] => idtac
      | _ => fail "STURDY-NO-ZERO-TERM: the newest value holds no zero term"
      end;
      let x := fresh "hz" in
      let H0 := fresh "Hzero_old" in
      let H := fresh "Hzero_new" in
      pose (x := e);
      assert (H0 : x = e) by reflexivity;
      assert (H : x = e) by reflexivity;
      clearbody x;
      rewrite ?Z.sub_0_r, ?Z.add_0_r in H;
      lazymatch type of H with
      | _ = ?v => zsetreg v ltac:(exact (eq_trans (eq_sym H) H0))
      end;
      clear H H0 x
  end.

(* EDITION 14 (its third file is the edition; the first two were trials; the module's name stays `ZGo11`; nothing
   of edition 13 is changed but the two places said here). ITS FAILURE WORDS, new: STURDY-NOT-SMALL,
   STURDY-NO-WRAP, STURDY-LOAD-BASE, STURDY-LOAD-NO-CHEAP (inside a run each is caught: the value stays as it
   is; the kit's own step word runs).
   THE FIRST TRIAL's NOTE (a converter's measure: in a context with several array facts and many arithmetic
   facts, a run stood for minutes at ONE table load). WHY: the kit's step word tries, at a load, first its plain
   memory facts (for each range fact of another base: a failing proof by the kit's arithmetic), then EVERY array
   fact of the load's width in the order the context has them, and a WRONG array ends only when the kit's
   arithmetic gives up on its index bound.
   THE CHEAP PASS AT A LOAD (`zgo_load_cheap`): the kit's own array rules, in the kit's own order, with the kit's
   own address words, and ONE change: the address equation and the index bound go to the kit's PLAIN solver
   (`lia_std`: no separation cases), so a wrong array is left in a moment. It is tried BEFORE the kit's step word,
   and ONLY where the kit's cheap plain-fact alternatives cannot apply (`zgo_load_guard`: no plain memory fact
   stands at the address as written, and no memory range fact of the same base is in hand). Where the cheap pass
   proves nothing, the kit's step word runs as in edition 13: nothing is lost. WHAT CAN DIFFER FROM EDITION 13:
   where a range fact of ANOTHER base and an array fact both cover the address, the array rule is now taken. *)
Ltac zgo_load_guard A :=
  lazymatch goal with
  | _ : mem_u64 _ _ A _ |- _ => fail "a plain memory fact stands at this address"
  | _ : mem_u32 _ _ A _ |- _ => fail "a plain memory fact stands at this address"
  | _ : mem_u16 _ _ A _ |- _ => fail "a plain memory fact stands at this address"
  | _ : mem_u8 _ _ A _ |- _ => fail "a plain memory fact stands at this address"
  | _ : mem_is _ _ A _ |- _ => fail "a plain memory fact stands at this address"
  | _ : rdn _ _ (w64 A) _ = Some _ |- _ => fail "a plain memory fact stands at this address"
  | _ => idtac
  end;
  tryif (match goal with
         | _ : mem_is _ _ ?a _ |- _ => zsame_base A a
         | _ : mem_zero _ _ ?a _ |- _ => zsame_base A a
         end)
  then fail "a memory range fact of the same base is in hand"
  else idtac.

(* SECOND TRIAL FILE (a diagnosis on the slow text, each alternative timed apart): (1) at the slow load the WRONG
   arrays cost the time: an array of another base passes the address equation (any index is an index) and its
   index bound is then decided NEITHER way: the plain solver and the kit's solver both run long before they give
   up. So the cheap pass now takes an array ONLY IF ITS BASE STANDS IN THE ADDRESS AS WRITTEN (`zgo_base_in`: the
   base's leftmost term, numeral addends taken off), proves the address equation by the ring's normal form (it
   fails at once where the rule's shape is not the address's), and gives the bound to the kit's own bound word.
   (2) THE SMALL-VALUE WORD after an instruction cost more than the load: where the newest value is a wrapped
   value that is NOT provably small, the kit's word fails only after every separation tier of the kit's
   arithmetic. `zgo_small` is the kit's small-value word, clause for clause, with the range goal given to the
   kit's first tier and then to the kit's plain `lia`: a value's range does not need the separation tiers. *)
Ltac zgo_root b :=
  lazymatch b with
  | ?x + ?c => lazymatch is_zlit_b c with
               | true => zgo_root x
               | _ => b
               end
  | _ => b
  end.

Ltac zgo_base_in A b :=
  let r := zgo_root b in
  lazymatch A with
  | context [r] => idtac
  | _ => fail "STURDY-LOAD-BASE: the array's base does not stand in the address"
  end.

Ltac zgo_arr_addr_cheap :=
  lazymatch goal with
  | |- ?A = ?b + ?k' * ?i =>
      zgo_load_guard A; zgo_base_in A b;
      (let e := zstrip_base A b in
       let x := zdivk e k' in
       unify i x; ring)
  end.

Ltac zgo_arr4_addr_cheap :=
  lazymatch goal with
  | |- ?A = ?b + 4 * ?i + ?off =>
      zgo_load_guard A; zgo_base_in A b;
      (let e := zstrip_base A b in
       let x := zdivk constr:(e - off) constr:(4) in
       unify i x; ring)
  | |- ?A = ?b + 4 * ?i =>
      zgo_load_guard A; zgo_base_in A b;
      (let e := zstrip_base A b in
       let x := zdivk e constr:(4) in
       unify i x; ring)
  end.

Ltac zgo_small_solve :=
  first [ zgo_t1
        | fail 1 "STURDY-NOT-SMALL: the value's range is not proved by the kit's first tier" ].

Ltac zgo_small :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, bv_swrap 32 ?e) :: _)) _ _) _ =>
      zsetreg e ltac:(symmetry; apply swrap32_small; zgo_small_solve)
  | |- realizes _ (zcfg _ _ (zupd _ ((_, bv_swrap 64 ?e) :: _)) _ _) _ =>
      zsetreg e ltac:(symmetry; apply swrap64_small; zgo_small_solve)
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e mod 18446744073709551616) :: _)) _ _) _ =>
      zsetreg e ltac:(symmetry; apply Z.mod_small; zgo_small_solve)
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e mod 4294967296) :: _)) _ _) _ =>
      zsetreg e ltac:(symmetry; apply Z.mod_small; zgo_small_solve)
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e mod 65536) :: _)) _ _) _ =>
      zsetreg e ltac:(symmetry; apply Z.mod_small; zgo_small_solve)
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e mod 256) :: _)) _ _) _ =>
      zsetreg e ltac:(symmetry; apply Z.mod_small; zgo_small_solve)
  | _ => fail "STURDY-NO-WRAP: the newest value is no wrapped value"
  end.

Ltac zgo_arr_cheap LEM k F E D :=
  match goal with
  | Ha : mem_arr k ?segs ?M ?base ?n ?f |- _ =>
      eapply (LEM segs _ _ _ _ _ _ _ _ _ _ base n f);
      [ exact F | exact E | exact D | zhalted | exact Ha
      | znorm; zgo_arr_addr_cheap
      | znorm; zgo_t1 | ]
  end.

Ltac zgo_arr_cheap_r LEM k F E D :=
  match goal with
  | Ha : mem_arr k ?segs ?M ?base ?n ?f |- _ =>
      eapply (LEM segs _ _ _ _ _ _ _ _ _ _ base n f);
      [ exact F | exact E | exact D | zhalted | exact Ha
      | znorm; zgo_arr_addr_cheap
      | znorm; zgo_t1 | znorm; zarr_range_tac | ]
  end.

Ltac zgo_arr4_cheap LEM F E D :=
  match goal with
  | Ha : mem_arr 4 ?segs ?M ?base ?n ?f |- _ =>
      eapply (LEM segs _ _ _ _ _ _ _ _ _ _ base n f);
      [ exact F | exact E | exact D | zhalted | exact Ha
      | znorm; zgo_arr4_addr_cheap
      | znorm; zgo_t1 | ]
  end.

(* the kit's array rules of each load kind, in the kit's order (IK/ITac.v `tstep_with`) *)
Ltac zgo_load_cheap_k F E D :=
  lazymatch type of D with
  | decode_any _ = Some (Load SZ1 false _ _ _, _) =>
      first [ zgo_arr_cheap_r zu_lbu_arr' 1 F E D | zgo_arr_cheap zu_lbu_arr 1 F E D
            | zgo_arr4_cheap zu_lbu_arr4_op F E D | zgo_arr4_cheap zu_lbu_arr4_bits F E D
            | zgo_arr_cheap zu_lbu_arr2_lo 2 F E D ]; znorm
  | decode_any _ = Some (Load SZ1 true _ _ _, _) =>
      zgo_arr_cheap zu_lb_arr 1 F E D; znorm
  | decode_any _ = Some (Load SZ2 false _ _ _, _) =>
      first [ zgo_arr_cheap_r zu_lhu_arr' 2 F E D | zgo_arr_cheap zu_lhu_arr 2 F E D
            | zgo_arr4_cheap zu_lhu_arr4_val F E D ]; znorm
  | decode_any _ = Some (Load SZ2 true _ _ _, _) =>
      first [ zgo_arr_cheap_r zu_lh_arr' 2 F E D | zgo_arr_cheap zu_lh_arr 2 F E D ]; znorm
  | decode_any _ = Some (Load SZ4 false _ _ _, _) =>
      first [ zgo_arr_cheap_r zu_lwu_arr' 4 F E D | zgo_arr_cheap zu_lwu_arr 4 F E D ]; znorm
  | decode_any _ = Some (Load SZ4 true _ _ _, _) =>
      first [ zgo_arr_cheap_r zu_lw_arr' 4 F E D | zgo_arr_cheap zu_lw_arr 4 F E D ]; znorm
  | decode_any _ = Some (Load SZ8 true _ _ _, _) =>
      zgo_arr_cheap zu_ld_arr 8 F E D; znorm
  | _ => fail "no array rule of the kit is for this instruction"
  end.

(* THIRD FILE: one failure word for the cheap pass, whatever made it fail (no array rule for the instruction; no
   array fact whose base stands in the address; a plain memory fact at the address; the rule's premises) *)
Ltac zgo_load_cheap F E D :=
  first [ zgo_load_cheap_k F E D
        | fail 1 "STURDY-LOAD-NO-CHEAP: no array fact with its base in the address takes this instruction" ].

(* the step of an instruction that is no branch and no register jump: at a load the cheap pass first *)
Ltac zgo_step1 F E D :=
  lazymatch type of D with
  | decode_any _ = Some (Load _ _ _ _ _, _) => first [ zgo_load_cheap F E D | tstep_with F E D ]
  | _ => tstep_with F E D
  end.

Ltac zgo_k F E D :=
  lazymatch type of D with
  | decode_any _ = Some (Branch _ _ _ _, _) =>
      first [ zbr_any F E D
            | assert_succeeds (zbr_premises F E D);
              fail 1 "STURDY-OPEN-BRANCH: the facts in hand decide this branch neither way"
            | fail 1 "STURDY-BRANCH-PREMISE: a premise of the branch rule other than its condition is not closed" ]
  | decode_any _ = Some (Jalr _ _ _, _) =>
      first [ tstep_with F E D | zret_with F E D
            | fail 1 "STURDY-NO-STEP: neither the kit's step nor its return applies at this instruction" ];
      try zdrop0; try zgo_small; try zlit_closed
  | _ =>
      first [ zgo_step1 F E D
            | fail 1 "STURDY-NO-STEP: the kit's step does not apply at this instruction" ];
      try zdrop0; try zgo_small; try zlit_closed
  end.

(* EDITION 7 (the non-author reader's asks D1 and D2): THE PC MUST BE A NUMERAL BEFORE ANY LOOKUP OR COMPUTATION
   ON IT (a jump can leave a pc that is no numeral: the run then fails with a word of its own); and each step
   and the handed-in tactic run under `once` (one success, no way back into them). *)
Ltac zpc_num :=
  let pc := zpc in
  first [ is_zlit pc | fail 1 "STURDY-PC-NOT-NUMERAL: the pc is no numeral" ].

Ltac zgo_one fd :=
  zpc_num; (let pc := zpc in fd pc zgo_k).

(* after one instruction: `tac`, or one more instruction, while the fuel lasts *)
Ltac zgo_until_n fd tac n :=
  lazymatch n with
  | O => fail "STURDY-FUEL-CONT: the fuel is spent before the continuation applies"
  | S ?m => once (zgo_one fd); tryif once tac then idtac else zgo_until_n fd tac m
  end.

Ltac zgo_to_n fd stop n :=
  zpc_num;
  (let pc := zpc in
   let b := eval vm_compute in (Z.eqb pc stop) in
   lazymatch b with
   | true => idtac
   | false =>
       lazymatch n with
       | O => fail "STURDY-FUEL-LABEL: the fuel is spent before the stop label"
       | S ?m => once (zgo_one fd); zgo_to_n fd stop m
       end
   | _ => fail "zgo: the comparison with the stop label gave no truth value"
   end).

(* EDITION 5: A RUN TO THE NEXT OPEN BRANCH: at least one instruction, then on until the next instruction is
   a branch that the facts in hand decide NEITHER way; it stops BEFORE that branch (the walk text then splits
   the case, and its next run takes the branch). Any other step that fails, fails the run; so does the fuel's
   end; so does an open branch at the very first instruction (a run of no instruction is no run). *)
Ltac zgo_branch_n fd n isfirst :=
  lazymatch n with
  | O => fail "STURDY-FUEL-BRANCH: the fuel is spent before an open branch"
  | S ?m =>
      zpc_num;
      (let pc := zpc in
       fd pc ltac:(fun F E D =>
         lazymatch type of D with
         | decode_any _ = Some (Branch _ _ _ _, _) =>
             tryif once (zbr_any F E D)
             then zgo_branch_n fd m false
             else (first [ assert_succeeds (zbr_premises F E D)
                         | fail 1 "STURDY-BRANCH-PREMISE: a premise of the branch rule other than its condition is not closed" ];
                   lazymatch isfirst with
                   | true => fail "STURDY-FIRST-OPEN-BRANCH: the first instruction is an open branch: no instruction is run"
                   | _ => idtac
                   end)
         | _ => once (zgo_k F E D); zgo_branch_n fd m false
         end))
  end.

Tactic Notation "zto_branch" tactic0(fd) :=
  let n' := eval cbv in 400%nat in zgo_branch_n fd n' true.

(* the same run with a FUEL numeral (edition 9): for must-fail texts only, like `zuntil_n` and `zgo_n` *)
Tactic Notation "zto_branch_n" tactic0(fd) constr(n) :=
  let n' := eval cbv in n in zgo_branch_n fd n' true.

Tactic Notation "zuntil_n" tactic0(fd) tactic3(tac) constr(n) :=
  let n' := eval cbv in n in zgo_until_n fd tac n'.

Tactic Notation "zuntil" tactic0(fd) tactic3(tac) :=
  let n' := eval cbv in 400%nat in zgo_until_n fd tac n'.

Tactic Notation "zuntil0" tactic0(fd) tactic3(tac) :=
  tryif once tac then idtac else (let n' := eval cbv in 400%nat in zgo_until_n fd tac n').

Tactic Notation "zgo_n" tactic0(fd) constr(stop) constr(n) :=
  let n' := eval cbv in n in
  lazymatch n' with
  | O => fail "zgo: no fuel"
  | S ?m => once (zgo_one fd); zgo_to_n fd stop m
  end.

Tactic Notation "zgo" tactic0(fd) constr(stop) :=
  let n' := eval cbv in 400%nat in once (zgo_one fd); zgo_to_n fd stop n'.

(* EDITION 10: VALUE HINTS. A hand walk text replaces, right after a certain step, the newest register value
   by an equal, nicer one with a proof from the model's facts (the kit's `zsetreg v ltac:(proof)`). A run
   cannot know such a value. THE HINT FORMS take a HINTS tactic and try it ONCE AFTER EACH INSTRUCTION that
   writes a register, before the driver's own small-value and closed-value words: a hint applies only where
   the newest value is provably the hinted one; where none applies nothing happens. So a hint names NO place:
   no step count, no register. (Edition 10 said here to write the hints inline, as the kit's value word with a
   proof: THAT FORM IS WITHDRAWN: see edition 11 below: a hint is `zhint <a named lemma>`.)
   The edition-9 words above are unchanged. *)
(* EDITION 11 (the non-author reader's read of edition 10 for cost; the lead's three cures; edition 10,
   , stays as it ran: IN THE TRIAL FOLDER THIS FILE IS `ZGo11`, beside edition 10's `ZGo`; in the
   package form it is the one driver text). WHAT WAS DEAR: edition 10 tried every hint after EVERY instruction that is no
   branch, and a hint that does not apply had to FAIL in its proof tactic ("hinted value = newest value" by a
   lemma or by `reflexivity`): nothing bounds that failure.
   (a) A HINT IS TRIED ONLY WHEN THE INSTRUCTION CHANGED THE REGISTER LIST (`zregl` before and after the step,
       compared as written), AND A HINT IS A REWRITE OF THE NEWEST VALUE, NOT A PROOF OF AN EQUATION:
       `zhint lem` takes a named lemma `.. -> machine form = nicer form` and rewrites with it in a COPY of the
       newest value (`zhint_rw`); the rewrite's own match of the lemma's left side IS the cheap test: where the
       form is not there, the hint fails at the match, before any side condition is tried; the side
       conditions go to `lia` (`zhint_by lem (closer)`: to `closer`). The hinted value is what the rewrite
       leaves: the text writes no value. `zhint_rw` takes a tactic of the hypothesis' name for a hint of
       several rewrites (bind it to a named local tactic OUTSIDE the run call).
   (b) THE CLOSERS FORMS `zuntil_c fd (app) (closer)` and `zuntil_hc fd (hints) (app) (closer)`: the run stops
       when `app` (the continuation's application alone) succeeds; then `closer` must SOLVE each premise that
       `app` left; a premise it does not solve FAILS the run with the word STURDY-CLOSER: the run never walks
       on past a join point whose continuation applied. (`zuntil` and `zuntil_h` stay: hand them the
       application alone and close the premises in the text after the run call.)
   (c) FUEL FORMS of the two hint forms, for must-fail and trial texts only: `zuntil_hn`, `zto_branch_hn`. *)
Ltac zregl :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ?l) _ _) _ => l
  | _ => constr:(tt)
  end.

Ltac znewest :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ => e
  | _ => fail "STURDY-NO-NEWEST: the state's register list has no newest value"
  end.

(* a value hint by rewriting: `rw` is a tactic that takes a hypothesis' name `H : x = newest value` (x a fresh
   variable) and rewrites in H; it must fail where the newest value has not the form it rewrites *)
Ltac zhint_rw rw :=
  idtac;
  let nv := znewest in
  let x := fresh "hx" in
  let H0 := fresh "Hhint_old" in
  let H := fresh "Hhint_new" in
  pose (x := nv);
  assert (H0 : x = nv) by reflexivity;
  assert (H : x = nv) by reflexivity;
  clearbody x;
  first [ rw H
        | fail 1 "STURDY-HINT-NO-FORM: the hint's rewrite does not apply to the newest value (its form is not there, or a side condition is not closed)" ];
  lazymatch type of H with
  | _ = ?v =>
      first [ constr_eq v nv; fail 1 "STURDY-HINT-NO-CHANGE: the hint's rewrite left the newest value as it was"
            | idtac ];
      zsetreg v ltac:(exact (eq_trans (eq_sym H) H0))
  end;
  clear H H0 x.

Ltac zhint_by lem closer := zhint_rw ltac:(fun H => rewrite lem in H by closer).
Ltac zhint lem := zhint_rw ltac:(fun H => rewrite lem in H by lia).

(* the hints are tried once, and only if the step changed the register list *)
Ltac zgo_hint l0 hint :=
  idtac;
  (let l1 := zregl in
   tryif constr_eq l0 l1 then idtac else (try (once hint))).

Ltac zgo_kh hint F E D :=
  lazymatch type of D with
  | decode_any _ = Some (Branch _ _ _ _, _) => zgo_k F E D
  | decode_any _ = Some (Jalr _ _ _, _) =>
      let l0 := zregl in
      (first [ tstep_with F E D | zret_with F E D
             | fail 1 "STURDY-NO-STEP: neither the kit's step nor its return applies at this instruction" ];
       zgo_hint l0 hint; try zdrop0; try zgo_small; try zlit_closed)
  | _ =>
      let l0 := zregl in
      (first [ zgo_step1 F E D
             | fail 1 "STURDY-NO-STEP: the kit's step does not apply at this instruction" ];
       zgo_hint l0 hint; try zdrop0; try zgo_small; try zlit_closed)
  end.

Ltac zgo_one_h fd hint :=
  zpc_num; (let pc := zpc in fd pc ltac:(fun F E D => zgo_kh hint F E D)).

Ltac zgo_until_hn fd hint tac n :=
  lazymatch n with
  | O => fail "STURDY-FUEL-CONT: the fuel is spent before the continuation applies"
  | S ?m => once (zgo_one_h fd hint); tryif once tac then idtac else zgo_until_hn fd hint tac m
  end.

Ltac zgo_branch_hn fd hint n isfirst :=
  lazymatch n with
  | O => fail "STURDY-FUEL-BRANCH: the fuel is spent before an open branch"
  | S ?m =>
      zpc_num;
      (let pc := zpc in
       fd pc ltac:(fun F E D =>
         lazymatch type of D with
         | decode_any _ = Some (Branch _ _ _ _, _) =>
             tryif once (zbr_any F E D)
             then zgo_branch_hn fd hint m false
             else (first [ assert_succeeds (zbr_premises F E D)
                         | fail 1 "STURDY-BRANCH-PREMISE: a premise of the branch rule other than its condition is not closed" ];
                   lazymatch isfirst with
                   | true => fail "STURDY-FIRST-OPEN-BRANCH: the first instruction is an open branch: no instruction is run"
                   | _ => idtac
                   end)
         | _ => once (zgo_kh hint F E D); zgo_branch_hn fd hint m false
         end))
  end.

Tactic Notation "zuntil_h" tactic0(fd) tactic3(hint) tactic3(tac) :=
  let n' := eval cbv in 400%nat in zgo_until_hn fd hint tac n'.

Tactic Notation "zto_branch_h" tactic0(fd) tactic3(hint) :=
  let n' := eval cbv in 400%nat in zgo_branch_hn fd hint n' true.

(* EDITION 11 (c): the two hint forms with a FUEL numeral: for must-fail and trial texts only *)
Tactic Notation "zuntil_hn" tactic0(fd) tactic3(hint) tactic3(tac) constr(n) :=
  let n' := eval cbv in n in zgo_until_hn fd hint tac n'.

Tactic Notation "zto_branch_hn" tactic0(fd) tactic3(hint) constr(n) :=
  let n' := eval cbv in n in zgo_branch_hn fd hint n' true.

(* EDITION 11 (b): THE CLOSERS FORMS. `app` is the continuation's application ALONE; the run stops at the first
   instruction after which it succeeds; `closer` is then run on EACH premise that `app` left and must solve
   it; one that it does not solve fails the run with STURDY-CLOSER (the run does not walk on). *)
Ltac zgo_closed closer :=
  first [ solve [ closer ]
        | fail 1 "STURDY-CLOSER: the continuation applied, but its closer does not solve one of its premises" ].

Ltac zgo_until_cn fd app closer n :=
  lazymatch n with
  | O => fail "STURDY-FUEL-CONT: the fuel is spent before the continuation applies"
  | S ?m => once (zgo_one fd);
            tryif once app then zgo_closed closer else zgo_until_cn fd app closer m
  end.

Ltac zgo_until_hcn fd hint app closer n :=
  lazymatch n with
  | O => fail "STURDY-FUEL-CONT: the fuel is spent before the continuation applies"
  | S ?m => once (zgo_one_h fd hint);
            tryif once app then zgo_closed closer else zgo_until_hcn fd hint app closer m
  end.

Tactic Notation "zuntil_c" tactic0(fd) tactic3(app) tactic3(closer) :=
  let n' := eval cbv in 400%nat in zgo_until_cn fd app closer n'.

Tactic Notation "zuntil_hc" tactic0(fd) tactic3(hint) tactic3(app) tactic3(closer) :=
  let n' := eval cbv in 400%nat in zgo_until_hcn fd hint app closer n'.

(* the closers form with a FUEL numeral: for must-fail and trial texts only *)
Tactic Notation "zuntil_cn" tactic0(fd) tactic3(app) tactic3(closer) constr(n) :=
  let n' := eval cbv in n in zgo_until_cn fd app closer n'.

(* EDITION 11 (d): THE BRANCH SPLIT. At an OPEN branch (where `zto_branch` stopped) a walk text whose facts
   do not decide the branch may split the case ON THE BRANCH's CONDITION ITSELF: `zbranch_split fd` is the
   kit's own split (`zcase_with`: the condition's two truth values, the branch taken each way) behind the
   driver's pc test: two goals, each with the condition's equation as a new hypothesis (find it by its form,
   not by its name). No direction and no register is written. At an instruction that is no branch it fails
   with a word of its own. *)
(* EDITION 12 (a converter's measure: the kit's own split word is RED at a branch whose condition is long: its
   last step does not take its own hypothesis; edition 11's `zbranch_split` was red there with it). THE SPLIT
   IS NOW DONE FIRST BY THE KIT's BRANCH RULE WITH ITS TRUTH VALUE LEFT OPEN: the condition premise is closed
   by "normal form, then reflexivity", which fills the truth value with the condition's own normal form; the
   case is split on that form (its equation is the new hypothesis); then the kit's two closing words. The
   kit's split word is tried second. Nothing else of edition 11 is changed; THE MODULE's NAME STAYS `ZGo11`
   (the texts' heads name it). *)
Ltac zgo_split_open F E D :=
  eapply (zu_branch_b _); [ zexact F | zexact E | zexact D | zhalted | znorm; reflexivity | ];
  lazymatch goal with
  | |- realizes _ (zcfg _ (if ?CN then _ else _) _ _ _) _ =>
      let Hsp := fresh "Hsplit" in destruct CN eqn:Hsp
  end;
  zcbv_iota; znorm.

Ltac zgo_split F E D :=
  lazymatch type of D with
  | decode_any _ = Some (Branch _ _ _ _, _) =>
      first [ zgo_split_open F E D
            | zcase_with F E D
            | fail 1 "STURDY-SPLIT: neither the open branch rule nor the kit's branch split applies at this branch" ]
  | _ => fail "STURDY-SPLIT-NO-BRANCH: the instruction at this pc is no branch"
  end.

Tactic Notation "zbranch_split" tactic0(fd) :=
  zpc_num; (let pc := zpc in fd pc zgo_split).

(* EDITION 13, SECOND FILE (a converter's ask; one word more in the hint word; nothing else is changed).
   A RUN "TO A CONTINUATION OR TO AN OPEN TEST": `zuntil_b fd (tac)`: at least one instruction; after each
   instruction `tac` is tried and ends the run where it applies; where the NEXT instruction is a test that the
   facts in hand decide neither way the run STOPS BEFORE IT with success (as `zto_branch` does). For a walk that
   must not assume the order of the code's pieces. A first instruction that is an open test fails with the word
   of the open-branch run; a branch premise that is not closed and the fuel's end give their own words.
   `zuntil_bn`: the same with a FUEL numeral, for must-fail and trial texts only.
   THE HINT WORD: where the handed-in rewrite does not find its form, `zhint_rw` now fails with a word of its own
   (STURDY-HINT-NO-FORM); inside a run that failure is still caught: the hint is not taken.
   THIRD FILE (two words only; the code's steps are the second file's): the zero-term word, called where the
   newest value holds no zero term, fails with a word of its own (STURDY-NO-ZERO-TERM; inside a run it is
   caught); STURDY-HINT-NO-FORM's sentence names both of its causes. *)
Ltac zgo_until_bn fd tac n isfirst :=
  lazymatch n with
  | O => fail "STURDY-FUEL-CONT: the fuel is spent before the continuation applies"
  | S ?m =>
      zpc_num;
      (let pc := zpc in
       fd pc ltac:(fun F E D =>
         lazymatch type of D with
         | decode_any _ = Some (Branch _ _ _ _, _) =>
             tryif once (zbr_any F E D)
             then (tryif once tac then idtac else zgo_until_bn fd tac m false)
             else (first [ assert_succeeds (zbr_premises F E D)
                         | fail 1 "STURDY-BRANCH-PREMISE: a premise of the branch rule other than its condition is not closed" ];
                   lazymatch isfirst with
                   | true => fail "STURDY-FIRST-OPEN-BRANCH: the first instruction is an open branch: no instruction is run"
                   | _ => idtac
                   end)
         | _ => once (zgo_k F E D); (tryif once tac then idtac else zgo_until_bn fd tac m false)
         end))
  end.

Tactic Notation "zuntil_b" tactic0(fd) tactic3(tac) :=
  let n' := eval cbv in 400%nat in zgo_until_bn fd tac n' true.

Tactic Notation "zuntil_bn" tactic0(fd) tactic3(tac) constr(n) :=
  let n' := eval cbv in n in zgo_until_bn fd tac n' true.

(* EDITION 15 (a measure: one text, the same bytes: 233 s with edition 14, 17.8 s when its runs to an open test
   took "open" as below; over the 300 s cap with edition 12). WHERE THE TIME WENT: at the test where such a run
   stops, the first tier decides neither way at once, and then the kit's whole arithmetic chain runs both ways
   before the run may call the test open.
   THE QUICK FORMS: `zto_branch_q fd`, `zto_branch_hq fd (hints)`, `zuntil_bq fd (tac)`: the same runs as
   `zto_branch`, `zto_branch_h`, `zuntil_b`, with ONE change of meaning: A TEST AT WHICH THE RUN MAY STOP IS ONE
   THAT THE KIT's FIRST TIER DECIDES NEITHER WAY (the kit's whole chain is not asked there). So a quick run stops
   where the plain run stops, OR EARLIER: before a test that only the kit's whole chain would decide. Use a quick
   form where the next stop is a test that the text then splits by a case of the model; a test that the whole
   chain alone decides is taken by the next plain run's first instruction (its own word tries the first tier and
   then the whole chain). Inside every run the tests are tried as before (first tier, then the whole chain): only
   the STOP is decided by the first tier. The plain forms are unchanged. The failure words are the plain forms'.
   `zto_branch_qn`, `zto_branch_hqn`, `zuntil_bqn`: with a FUEL numeral, for must-fail and trial texts only. *)
Ltac zbr_cheap_any F E D := first [ zbr_cheap true F E D | zbr_cheap false F E D ].

Ltac zgo_branch_qn fd n isfirst :=
  lazymatch n with
  | O => fail "STURDY-FUEL-BRANCH: the fuel is spent before an open branch"
  | S ?m =>
      zpc_num;
      (let pc := zpc in
       fd pc ltac:(fun F E D =>
         lazymatch type of D with
         | decode_any _ = Some (Branch _ _ _ _, _) =>
             tryif once (zbr_cheap_any F E D)
             then zgo_branch_qn fd m false
             else (first [ assert_succeeds (zbr_premises F E D)
                         | fail 1 "STURDY-BRANCH-PREMISE: a premise of the branch rule other than its condition is not closed" ];
                   lazymatch isfirst with
                   | true => fail "STURDY-FIRST-OPEN-BRANCH: the first instruction is an open branch: no instruction is run"
                   | _ => idtac
                   end)
         | _ => once (zgo_k F E D); zgo_branch_qn fd m false
         end))
  end.

Ltac zgo_branch_hqn fd hint n isfirst :=
  lazymatch n with
  | O => fail "STURDY-FUEL-BRANCH: the fuel is spent before an open branch"
  | S ?m =>
      zpc_num;
      (let pc := zpc in
       fd pc ltac:(fun F E D =>
         lazymatch type of D with
         | decode_any _ = Some (Branch _ _ _ _, _) =>
             tryif once (zbr_cheap_any F E D)
             then zgo_branch_hqn fd hint m false
             else (first [ assert_succeeds (zbr_premises F E D)
                         | fail 1 "STURDY-BRANCH-PREMISE: a premise of the branch rule other than its condition is not closed" ];
                   lazymatch isfirst with
                   | true => fail "STURDY-FIRST-OPEN-BRANCH: the first instruction is an open branch: no instruction is run"
                   | _ => idtac
                   end)
         | _ => once (zgo_kh hint F E D); zgo_branch_hqn fd hint m false
         end))
  end.

Ltac zgo_until_bqn fd tac n isfirst :=
  lazymatch n with
  | O => fail "STURDY-FUEL-CONT: the fuel is spent before the continuation applies"
  | S ?m =>
      zpc_num;
      (let pc := zpc in
       fd pc ltac:(fun F E D =>
         lazymatch type of D with
         | decode_any _ = Some (Branch _ _ _ _, _) =>
             tryif once (zbr_cheap_any F E D)
             then (tryif once tac then idtac else zgo_until_bqn fd tac m false)
             else (first [ assert_succeeds (zbr_premises F E D)
                         | fail 1 "STURDY-BRANCH-PREMISE: a premise of the branch rule other than its condition is not closed" ];
                   lazymatch isfirst with
                   | true => fail "STURDY-FIRST-OPEN-BRANCH: the first instruction is an open branch: no instruction is run"
                   | _ => idtac
                   end)
         | _ => once (zgo_k F E D); (tryif once tac then idtac else zgo_until_bqn fd tac m false)
         end))
  end.

Tactic Notation "zto_branch_q" tactic0(fd) :=
  let n' := eval cbv in 400%nat in zgo_branch_qn fd n' true.

Tactic Notation "zto_branch_qn" tactic0(fd) constr(n) :=
  let n' := eval cbv in n in zgo_branch_qn fd n' true.

Tactic Notation "zto_branch_hq" tactic0(fd) tactic3(hint) :=
  let n' := eval cbv in 400%nat in zgo_branch_hqn fd hint n' true.

Tactic Notation "zto_branch_hqn" tactic0(fd) tactic3(hint) constr(n) :=
  let n' := eval cbv in n in zgo_branch_hqn fd hint n' true.

Tactic Notation "zuntil_bq" tactic0(fd) tactic3(tac) :=
  let n' := eval cbv in 400%nat in zgo_until_bqn fd tac n' true.

Tactic Notation "zuntil_bqn" tactic0(fd) tactic3(tac) constr(n) :=
  let n' := eval cbv in n in zgo_until_bqn fd tac n' true.
