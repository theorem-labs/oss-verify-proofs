(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (bsb_bound restated over the launch's process input, mmap base, entry and brk with the launch premises, its bound now 2101782 bytes, with new lemmas block_head_size_le, launch_sp_le_top and launch_top_minus_sp; the using attributes dropped from the lemmas; the comments blanked for export written back in full). *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StreamExec MmapSim WallSim StreamSim DrainSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.

Import ListNotations.
Open Scope bv_scope.

Section WithFP1.
Context {fx : FPState}.

(* ######################################################################### *)
(* Chain-relation entry ([chain_step]) and pc literal normalization          *)
(* ######################################################################### *)

(** One step into whichever chain relation the current goal targets.
    Superset of every per-example [chain_step]/[step_intro]: [msteps]
    (plain instruction stream), [to_wexit] (write-then-exit, CatSim),
    [twm]/[tmw] (single mmap, MmapSim), [StreamSim.to_wr]/[StreamSim.to_rd]
    (unbounded stream loop), [DrainSim.to_out]/[DrainSim.to_rd] (drain-loop),
    [to_exit] (exit-only, ExitSim). *)
End WithFP1.
Ltac chain_step :=
  first [ eapply mst_step
        | eapply tw_step
        | eapply twm_step
        | eapply MmapSim.twmt_step
        | eapply tmw_step
        | eapply StreamSim.twr_step
        | eapply StreamSim.trd_step
        | eapply WallSim.twt_step
        | eapply WallSim.twe_step
        | eapply DrainSim.tout_step
        | eapply DrainSim.trd_step
        | eapply te_step ].

Section WithFP2.
Context {fx : FPState}.

(** Backward-compatible alias: several examples name this entry point
    [step_intro] instead of [chain_step]. *)
End WithFP2.
Ltac step_intro := chain_step.

Section WithFP3.
Context {fx : FPState}.

(* ######################################################################### *)
(* Safe vm_compute                                                          *)
(* ######################################################################### *)

(** Expand every let-bound context definition ([set]-introduced)
    mentioned in [p] to its body, recursively.  Closedness must be
    judged on the term the vm would actually reduce, and [vm_compute]
    unfolds context definitions — so a [set]-bound variable is as
    closed as its body. *)
End WithFP3.
Ltac expand_ctx_defs p :=
  match goal with
  | H := _ |- _ =>
      lazymatch p with
      | context [H] => let p' := eval unfold H in p in expand_ctx_defs p'
      end
  | _ => p
  end.

Section WithFP4.
Context {fx : FPState}.

(** Succeeds iff [p] is CLOSED as far as the vm is concerned: after
    expanding [set]-bound definitions it mentions no context variable
    and no evar.  This is the guard that makes [vm_compute] safe:
    pointed at an OPEN bv term, [vm_compute] does not get stuck and
    fail, it allocates until the machine dies — and [timeout] does NOT
    reliably stop it (the vm runs as C code that OCaml's signal
    delivery often fails to preempt; measured both ways on the same
    box, same term).  So the term must be proved closed BEFORE the vm
    ever sees it.

    It does not use the stdpp-style [exfalso; clear; pose p] probe,
    which (a) rebuilds the proof state on every call, and (b) fails on
    CLOSED terms whenever an evar in the goal depends on the context
    ([clear] refuses) — the normal state of a chain proof
    mid-[eexists], so that probe cannot guard the per-step paths.
    This implementation only pattern-matches the
    context, so it has neither failure mode. *)
End WithFP4.
Ltac check_closed_term p :=
  let p' := expand_ctx_defs p in
  tryif has_evar p' then
    fail 0 "check_closed_term:" p "contains an evar"
  else tryif match goal with
             | H : _ |- _ => lazymatch p' with context [H] => idtac end
             end
  then fail 0 "check_closed_term:" p "mentions a context variable"
  else idtac.

Section WithFP5.
Context {fx : FPState}.

(** The safe [eval vm_compute in t]: identical result, but [t] is
    checked closed first, so the vm can neither diverge on a symbolic
    bv term nor meet an evar.  Usable in value position wherever
    [eval vm_compute in] is; on an open term it fails fast instead,
    which a caller's [try]/[match]-backtracking absorbs.  Every
    value-position vm reduction of a caller-supplied term in this file
    goes through this — keep it that way. *)
End WithFP5.
Ltac vm_eval t :=
  let _ := match goal with _ => check_closed_term t end in
  eval vm_compute in t.

Section WithFP6.
Context {fx : FPState}.

(** Build the numeral-notation literal ([@BV 64 z I]-shaped) equal to a
    CLOSED word term [p] (fails fast when [p] is open).  Note the two
    normal forms of a computed word are NOT interconvertible:
    [Z_to_bv 64 z] carries the opaque [Z_to_bv_obligation_1] wf proof
    while a numeral literal carries the (vm-cast) [I] — so a chained
    machine state can only match a fetch lemma's literal pc up to a
    PROPOSITIONAL rewrite, never [change]. *)
End WithFP6.
Ltac word_lit p :=
  let u := vm_eval (bv_unsigned p) in
  constr:(@BV 64 u ltac:(vm_compute; exact I)).

Section WithFP7.
Context {fx : FPState}.

(** Body shared by [wlit]/[wlits]: replace redex [p] with its literal
    form.  [word_lit] fails fast on an open [p], so the [by] script
    only ever sees a closed equation. *)
End WithFP7.
Ltac wlit_replace p :=
  let l := word_lit p in
  replace p with l by (apply bv_eq; vm_compute; reflexivity).

Section WithFP8.
Context {fx : FPState}.

(** Rewrite a closed word subterm of the goal to its literal form
    (no-op when it already is one, or when [p] is open). *)
End WithFP8.
Ltac wlit p :=
  try (lazymatch p with
       | @BV _ _ _ => idtac
       | _ => wlit_replace p
       end).

Section WithFP9.
Context {fx : FPState}.

(** Normalize every closed computed-value redex in the goal to its
    literal form.  Open, sp-symbolic redexes fail [word_lit]'s
    closedness guard and are skipped — they are [sp_norm]'s job. *)
End WithFP9.
Ltac wlits :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_replace (v_addi a b)
  | |- context [btgt ?a ?b] => wlit_replace (btgt a b)
  | |- context [v_jalr ?a ?b] => wlit_replace (v_jalr a b)
  | |- context [v_auipc ?a ?b] => wlit_replace (v_auipc a b)
  end.

Section WithFP10.
Context {fx : FPState}.

(** Normalize the next-pc at the head of whichever chain relation the
    goal exposes to its literal form (so the next step's fetch-lemma
    literal matches by conversion).  Superset of every per-example
    [norm_pc]: tries every goal-head/arity combination across the
    examples (the two [to_rd] arities are
    [StreamSim.to_rd segs LH cnt ms] vs
    [DrainSim.to_rd segs cnt f out ec LH a ms] — same name, different
    section variables, hence qualified here to disambiguate). *)
(** Evar guard for [norm_pc]: when the machine-state position of the
    chain goal contains an evar (e.g. [norm_pc] called before the
    [eexists]/instantiation that pins the state), touching it with
    [replace] lets later unification blow up — so [norm_pc] must no-op
    instead.  Evar-free states behave exactly as before. *)
End WithFP10.
Ltac norm_pc_state st :=
  tryif has_evar st then idtac
  else lazymatch st with
       | mkst _ ?p _ _ => wlit p
       | _ => idtac
       end.
Ltac norm_pc :=
  try lazymatch goal with
  | |- msteps _ ?st _ => norm_pc_state st
  | |- to_wexit _ ?st _ _ => norm_pc_state st
  | |- twm _ ?st _ _ _ => norm_pc_state st
  | |- MmapSim.twm_pend _ ?st _ _ _ _ => norm_pc_state st
  | |- MmapSim.twm_tail _ ?st _ _ _ _ => norm_pc_state st
  | |- tmw _ ?st _ _ _ _ _ => norm_pc_state st
  | |- StreamSim.to_wr _ _ _ ?st => norm_pc_state st
  | |- StreamSim.to_rd _ _ _ ?st => norm_pc_state st
  | |- WallSim.to_wall _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wall_tail _ _ ?st _ _ => norm_pc_state st
  | |- WallSim.to_wallexit _ _ _ _ ?st => norm_pc_state st
  | |- to_exit _ _ ?st => norm_pc_state st
  | |- DrainSim.to_out _ _ ?st => norm_pc_state st
  | |- DrainSim.to_rd _ _ _ _ _ _ _ ?st => norm_pc_state st
  end.

Section WithFP12.
Context {fx : FPState}.

(* ######################################################################### *)
(* Single-instruction steps                                                  *)
(* ######################################################################### *)

(** Post-step simplification of decode-literal register guards
    ([if bv_eqb rd 0 ...] with rd a numeral) before pc normalization. *)
(** [cbn] cannot reduce these guards — [bv_unsigned] is a simpl-never
    projection over a vm-cast literal — so the boolean is vm-computed
    and the [if] collapsed by [change] (plain conversion). *)
End WithFP12.
Ltac reduce_bv_eqb_ifs :=
  repeat match goal with
  | |- context [if bv_eqb ?a ?b then ?x else ?y] =>
      lazymatch a with
      | @BV _ _ _ =>
          lazymatch b with
          | @BV _ _ _ =>
              let v := eval vm_compute in (bv_eqb a b) in
              lazymatch v with
              | true => change (if bv_eqb a b then x else y) with x
              | false => change (if bv_eqb a b then x else y) with y
              end
          end
      end
  end.

Section WithFP13.
Context {fx : FPState}.

(** [rewrite ?skipn_O]: several loop proofs hit a leftover [skipn 0]
    redex after a chunk step; the [?] form only fires when the redex
    exists, so it does not change other invocations. *)
End WithFP13.
Ltac step_simpl := reduce_bv_eqb_ifs; rewrite ?skipn_O; norm_pc.

Section WithFP14.
Context {fx : FPState}.

(** The instruction alternation of [stepi], tried in order.  Kept as a
    separate tactic so [stepi] can use it as the fallback behind the
    decode-shape dispatch below. *)
End WithFP14.
Ltac stepi_search F D :=
  first
    [ exact (step_addi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sub _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_auipc _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_andi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sltiu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_xori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)
    (* slti/srai, the register-register
       ALU ops, the remaining 32-bit ops, and the (premise-free)
       M-extension ops.  divu/remu carry a divisor-nonzero premise, so
       they live in [stepi]'s dispatch only. *)
    | exact (step_slti _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srai _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_and _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_xor _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sll _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srl _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sra _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slt _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sltu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_addw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sllw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srlw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sraw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_slliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_srliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_sraiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulh _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulhsu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulhu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_div _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_rem _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_mulw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_divw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_divuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_remw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | exact (step_remuw _ _ _ _ _ _ _ _ _ F eq_refl D) ].

Section WithFP15.
Context {fx : FPState}.

(** One non-branching ALU step inside a chain. Superset of every
    per-example instruction alternation.

    PERFORMANCE: the alternation is DISPATCHED on the decode lemma's
    shape rather than searched.  Every [exact] attempt elaborates its
    whole conclusion — which mentions the full machine state and memory
    image — before it can fail on the [decode_any] premise, so a wrong
    alternative is nearly as expensive as the right one.  Picking the
    single applicable lemma from [type of D] turns up to 14 attempts
    into one (an [Auipc] step, 5th in a searched list, costs ~4 s).
    Shapes not listed here fall through to [stepi_search], so the
    tactic remains a superset of the alternation. *)
(** Coverage note: the dispatch covers every OpImm /
    ShiftImm / Op / OpImm32 / ShiftImm32 / Op32 / Mul / Mul32 shape
    with a step lemma.  The [divu]/[remu] arms are the one exception
    to "closes the step goal": RISC-V defines division by zero, but
    their value shapes ([v_divu]/[v_remu]) do not, so those lemmas
    carry a divisor-nonzero premise.  The arm tries [assumption]/[lia]
    on it and otherwise LEAVES it as an extra goal (ordered before the
    continuation of the chain). *)
End WithFP15.
Ltac stepi F D :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
        exact (step_addi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
        exact (step_andi _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) =>
        exact (step_ori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) =>
        exact (step_xori _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_SLT _ _ _, _) =>
        exact (step_slti _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) =>
        exact (step_sltiu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
        exact (step_add _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
        exact (step_sub _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_AND _ _ _, _) =>
        exact (step_and _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_OR _ _ _, _) =>
        exact (step_or _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_XOR _ _ _, _) =>
        exact (step_xor _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLL _ _ _, _) =>
        exact (step_sll _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SRL _ _ _, _) =>
        exact (step_srl _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SRA _ _ _, _) =>
        exact (step_sra _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLT _ _ _, _) =>
        exact (step_slt _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op ALU_SLTU _ _ _, _) =>
        exact (step_sltu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_ADD _ _ _, _) =>
        exact (step_addw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SUB _ _ _, _) =>
        exact (step_subw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SLL _ _ _, _) =>
        exact (step_sllw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SRL _ _ _, _) =>
        exact (step_srlw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Op32 ALU_SRA _ _ _, _) =>
        exact (step_sraw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (OpImm32 _ _ _, _) =>
        exact (step_addiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
        exact (step_slli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
        exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) =>
        exact (step_srai _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SLL _ _ _, _) =>
        exact (step_slliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SRL _ _ _, _) =>
        exact (step_srliw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (ShiftImm32 ALU_SRA _ _ _, _) =>
        exact (step_sraiw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Auipc _ _, _) =>
        exact (step_auipc _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Lui _ _, _) =>
        exact (step_lui _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MUL _ _ _, _) =>
        exact (step_mul _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULH _ _ _, _) =>
        exact (step_mulh _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULHSU _ _ _, _) =>
        exact (step_mulhsu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_MULHU _ _ _, _) =>
        exact (step_mulhu _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_DIV _ _ _, _) =>
        exact (step_div _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_REM _ _ _, _) =>
        exact (step_rem _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul M_DIVU _ _ _, _) =>
        eapply step_divu;
        [ exact F | reflexivity | exact D | try first [ assumption | lia ] ]
    | decode_any _ = Some (Mul M_REMU _ _ _, _) =>
        eapply step_remu;
        [ exact F | reflexivity | exact D | try first [ assumption | lia ] ]
    | decode_any _ = Some (Mul32 M_MUL _ _ _, _) =>
        exact (step_mulw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_DIV _ _ _, _) =>
        exact (step_divw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_DIVU _ _ _, _) =>
        exact (step_divuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_REM _ _ _, _) =>
        exact (step_remw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | decode_any _ = Some (Mul32 M_REMU _ _ _, _) =>
        exact (step_remuw _ _ _ _ _ _ _ _ _ F eq_refl D)
    | _ => stepi_search F D
    end
  | step_simpl ].

Section WithFP16.
Context {fx : FPState}.

(** One ALU step with the written value pre-normalized, proof
    obligation left to the caller-supplied [tac].  (The value parameter
    is named [vv] to avoid capturing the lemmas' [v] binder.)
    DISPATCHED (like [stepi]) across the whole [SeqExec.step_*_at]
    family, which all share the same premise shape.  The fallback uses
    [step_addi_at] for shapes without an [_at] lemma. *)
End WithFP16.
Ltac stepiv F D vv tac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (OpImm ALU_ADD _ _ _, _) =>
        eapply step_addi_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_AND _ _ _, _) =>
        eapply step_andi_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_OR _ _ _, _) =>
        eapply step_ori_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_XOR _ _ _, _) =>
        eapply step_xori_at with (v := vv)
    | decode_any _ = Some (OpImm ALU_SLTU _ _ _, _) =>
        eapply step_sltiu_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SLL _ _ _, _) =>
        eapply step_slli_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SRL _ _ _, _) =>
        eapply step_srli_at with (v := vv)
    | decode_any _ = Some (ShiftImm ALU_SRA _ _ _, _) =>
        eapply step_srai_at with (v := vv)
    | decode_any _ = Some (Op ALU_ADD _ _ _, _) =>
        eapply step_add_at with (v := vv)
    | decode_any _ = Some (Op ALU_SUB _ _ _, _) =>
        eapply step_sub_at with (v := vv)
    | decode_any _ = Some (OpImm32 _ _ _, _) =>
        eapply step_addiw_at with (v := vv)
    | decode_any _ = Some (Mul M_MUL _ _ _, _) =>
        eapply step_mul_at with (v := vv)
    | decode_any _ = Some (Lui _ _, _) =>
        eapply step_lui_at with (v := vv)
    | decode_any _ = Some (Auipc _ _, _) =>
        eapply step_auipc_at with (v := vv)
    | _ => eapply step_addi_at with (v := vv)
    end;
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP17.
Context {fx : FPState}.

(** [addiw] step with the written value pre-normalized ([step_addiw_at]). *)
End WithFP17.
Ltac stepiwv F D vv tac :=
  chain_step;
  [ reflexivity
  | eapply step_addiw_at with (v := vv);
    [ exact F | reflexivity | exact D | reflexivity | tac ]
  | step_simpl ].

Section WithFP18.
Context {fx : FPState}.

(** Unconditional jump ([jal]).  The [x0] (no-link) form uses
    [step_jal_x0]; a LINKING [jal] (rd <> x0, the call idiom)
    falls through to [SeqExec.step_jal_link], whose
    [if bv_eqb rd 0] writeback guard [step_simpl] collapses. *)
End WithFP18.
Ltac stepj F D :=
  chain_step;
  [ reflexivity
  | first [ exact (step_jal_x0 _ _ _ _ _ _ _ F eq_refl D)
          | exact (step_jal_link _ _ _ _ _ _ _ _ F eq_refl D) ]
  | step_simpl ].

Section WithFP19.
Context {fx : FPState}.

(** Indirect jump ([jalr]), target named by the caller (it is a
    register value, so unlike a [jal] target it is not computable from
    the decode lemma alone): [tac] proves [getr regs rs1 = tgt].
    Dispatches between the [x0] (ret / tail-jump) and linking (call
    through a function pointer) forms.  NOTE: [norm_pc] vm-computes the
    next pc, so [tgt] must be a CLOSED word — resolve the register to a
    literal first (the same discipline as every fetch pc). *)
End WithFP19.
Ltac stepjr F D tv tac :=
  chain_step;
  [ reflexivity
  | first [ eapply step_jalr_x0 with (tgt := tv);
            [ exact F | reflexivity | exact D | tac ]
          | eapply step_jalr_link with (tgt := tv);
            [ exact F | reflexivity | exact D | reflexivity | tac ] ]
  | step_simpl ].

Section WithFP20.
Context {fx : FPState}.

(* ######################################################################### *)
(* sp-arithmetic normalization                                               *)
(* ######################################################################### *)

(** [bv_unsigned (Z_to_bv 64 z)] collapses to [z] when in range —
    the glue that lets nested [v_addi] rewrites feed their own side
    conditions to [lia]. *)
Lemma u_Z2bv : forall z, (0 <= z)%Z -> (z < 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hlo Hhi. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. apply Z.mod_small. split; [exact Hlo|].
  exact Hhi.
Qed.

(** Literal-immediate corollaries of [SeqExec.v_addi_m], one per small
    negative-immediate constant used across the examples ([rewrite]
    needs the LHS stated with a literal [-k]).  Conclusions are in the
    [Z_to_bv 64 (...)] canonical form. *)
Lemma v_addi_m1 : forall x, (1 <= bv_unsigned x)%Z ->
  v_addi x (-1) = Z_to_bv 64 (bv_unsigned x - 1).
Proof. intros x H1. apply (v_addi_m x 1); lia. Qed.

Lemma v_addi_m16 : forall x, (16 <= bv_unsigned x)%Z ->
  v_addi x (-16) = Z_to_bv 64 (bv_unsigned x - 16).
Proof. intros x H16. apply (v_addi_m x 16); lia. Qed.

Lemma v_addi_m32 : forall x, (32 <= bv_unsigned x)%Z ->
  v_addi x (-32) = Z_to_bv 64 (bv_unsigned x - 32).
Proof. intros x H32. apply (v_addi_m x 32); lia. Qed.

Lemma v_addi_m48 : forall x, (48 <= bv_unsigned x)%Z ->
  v_addi x (-48) = Z_to_bv 64 (bv_unsigned x - 48).
Proof. intros x H48. apply (v_addi_m x 48); lia. Qed.

Lemma v_addi_m64 : forall x, (64 <= bv_unsigned x)%Z ->
  v_addi x (-64) = Z_to_bv 64 (bv_unsigned x - 64).
Proof. intros x H64. apply (v_addi_m x 64); lia. Qed.

Lemma v_addi_m80 : forall x, (80 <= bv_unsigned x)%Z ->
  v_addi x (-80) = Z_to_bv 64 (bv_unsigned x - 80).
Proof. intros x H80. apply (v_addi_m x 80); lia. Qed.

(** Non-negative immediate, term-level form of [PropExec.v_addi_nneg]. *)
Lemma v_addi_nneg_t : forall x imm, (0 <= imm)%Z ->
  (bv_unsigned x + imm < 2^64)%Z ->
  v_addi x imm = Z_to_bv 64 (bv_unsigned x + imm).
Proof. intros x imm _ _. reflexivity. Qed.

(** Collapse the [bv_unsigned (Z_to_bv 64 _)] projections a rewrite
    chain leaves behind (side conditions from window bounds via lia). *)
End WithFP20.
Ltac u_norm := repeat rewrite u_Z2bv by lia.

Section WithFP21.
Context {fx : FPState}.

(** Reduce [bv_signed]/[bv_unsigned] of encoded-immediate LITERALS to Z
    numerals (by conversion), so the [v_addi_m*] rewrites below see the
    literal [-k] and [lia] sees numerals. *)
End WithFP21.
Ltac imm_norm :=
  repeat match goal with
  | |- context [bv_signed ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_signed b) in
          change (bv_signed b) with v
      end
  | |- context [bv_unsigned ?b] =>
      lazymatch b with
      | @BV _ _ _ =>
          let v := eval vm_compute in (bv_unsigned b) in
          change (bv_unsigned b) with v
      end
  end.

Section WithFP22.
Context {fx : FPState}.

(** Normalize nested [v_addi] expressions over an abstract in-window sp,
    innermost occurrence first (the window bounds must be in context for
    the [lia] side conditions). *)
End WithFP22.
Ltac sp_norm :=
  imm_norm;
  repeat (match goal with
  | |- context [v_addi ?x ?i] =>
      lazymatch x with
      | context [v_addi _ _] => fail
      | _ => first [ rewrite (v_addi_m80 x) by (u_norm; lia)
                   | rewrite (v_addi_m64 x) by (u_norm; lia)
                   | rewrite (v_addi_m48 x) by (u_norm; lia)
                   | rewrite (v_addi_m32 x) by (u_norm; lia)
                   | rewrite (v_addi_m16 x) by (u_norm; lia)
                   | rewrite (v_addi_m1 x) by (u_norm; lia)
                   | rewrite (v_addi_nneg_t x i) by (u_norm; lia) ]
      end
  end; u_norm; cbn [Z.to_N]).

Section WithFP23.
Context {fx : FPState}.

(** Same as [stepiv], but with the value-obligation proof script baked in. *)
End WithFP23.
Ltac stepi_at F D val :=
  chain_step;
  [ reflexivity
  | eapply step_addi_at with (v := val);
    [ exact F | reflexivity | exact D
    | reflexivity
    | getr_resolve; regupd_resolve; reduce_bv_eqb_ifs; sp_norm;
      first [ reflexivity | lia | f_equal; lia
            | apply bv_eq;
              lazymatch goal with |- ?g => check_closed_term g end;
              vm_compute; reflexivity ] ]
  | step_simpl ].

Section WithFP24.
Context {fx : FPState}.

(* ######################################################################### *)
(* Consolidated closing tactics                                             *)
(* ######################################################################### *)

(** Close a word/byte equation by unsigned comparison (the
    `replace ... by bveq` closer used across the examples).

    Triage by [check_closed_term], because [vm_compute] on an OPEN bv
    term — the usual cause being a register projection that was never
    resolved, so a value still reads [getr (regupd ... regs ...) r]
    with [regs] abstract — does not get stuck and fail, it allocates
    until the machine dies.  There is no Rocq-level error to read
    afterwards ("Fatal error: allocation failure during minor GC", if
    anything), and because the tactic is usually buried in a
    [replace ... by bveq] the call site is invisible in the crash; one
    such call can make an entire example file uncompilable and take
    the machine down with it.  (The guard is usable on this per-step
    path because it does not use a [clear]-based implementation, which
    fails on closed terms in evar-laden contexts; see its docstring.)

    - CLOSED goal: [vm_compute; reflexivity].  No wall-clock limit guards
      it (a time limit can fail a check on a loaded machine); the
      closedness test above is the guard, and a legitimate call here is
      small (a whole example file, with dozens of them, compiles in
      single-digit seconds).
    - evar: fail outright (the norm_pc-before-eexists trap; both the vm
      and unification-based closers misbehave on it).
    - open, evar-free: close by kernel conversion only, never the vm —
      see the inline comment. *)
End WithFP24.
Ltac bveq :=
  apply bv_eq;
  lazymatch goal with
  | |- ?g =>
      tryif check_closed_term g then
        first
          [ (vm_compute; reflexivity)
          | fail 1 "bveq: vm_compute did not close this closed goal; "
                   "if it is runaway-large, reduce it first." ]
      else tryif has_evar g then
        fail 1 "bveq: the goal contains an evar — vm_compute must not "
               "see it; instantiate the machine state (eexists / "
               "chain_step) before normalizing."
      else
        (* Open but evar-free.  The vm must not run — on an open bv
           term it allocates until the machine dies.  Kernel conversion
           decides the SAME relation ([vm_compute] is only a strategy)
           but gets STUCK on a variable instead of allocating, so plain
           [reflexivity] is the safe closer for the stuck-but-
           convertible class this position sees (e.g. an
           [alloc_fd (m_fds (init_model ... inp))] projection whose
           value never forces the abstract [inp]). *)
        first
          [ reflexivity
          | fail 1 "bveq: the goal is OPEN (it mentions a context "
                   "variable) and kernel conversion did not close it — "
                   "resolve the register and memory projections first "
                   "(getr_resolve, regupd_resolve) and try again." ]
  end.

Section WithFP25.
Context {fx : FPState}.

(* Smoke tests: a closed equation still closes, and an unresolved
   projection fails — via the closedness guard, before the vm ever
   runs — rather than being accepted.  Same style as SeqExec's
   [getr_resolve]/[regupd_resolve] tests. *)
Goal v_addi (Z_to_bv 64 5) 3 = Z_to_bv 64 8.
Proof. bveq. Abort.
Goal forall regs (v : word), getr (regupd regs 11 v) 11 = v.
Proof. intros. assert_fails bveq. getr_resolve. reflexivity. Abort.

(* Smoke tests for the closedness guard itself: closed
   terms pass — including [set]-bound variables with closed bodies,
   which the vm unfolds, and closed terms probed while the goal holds
   an evar (the shape a [clear]-based guard fails on) —
   while context variables, open [set] bodies, and evars all fail
   fast.  No test exercises an actual open vm run: that is the
   machine-killing divergence the guard exists to prevent. *)
Goal forall v : word, exists w : word, w = v.
Proof.
  intros v. eexists.
  check_closed_term (v_addi (Z_to_bv 64 5) 3).
  assert_fails (check_closed_term (v_addi v 4)).
  lazymatch goal with |- ?g => assert_fails (check_closed_term g) end.
  set (k := Z_to_bv 64 7).
  check_closed_term (v_addi k 1).
  set (k2 := v_addi v 1).
  assert_fails (check_closed_term (v_addi k2 1)).
  let u := vm_eval (bv_unsigned (v_addi (Z_to_bv 64 5) 3)) in
  lazymatch u with 8%Z => idtac end.
  (* NB: not [assert_fails (let u := ...)] — Ltac evaluates a [let]
     argument eagerly, before the combinator can catch its failure; the
     lazy contexts the real call sites use ([try], match-arm bodies)
     are what absorb a [vm_eval] failure. *)
  try (let u := vm_eval (bv_unsigned (v_addi v 4)) in
       fail 1 "vm_eval accepted an open term").
Abort.

(* The literal normalizers skip open redexes instead of feeding them
   to the vm: [wlit] no-ops on one, and [wlits] still rewrites the
   closed redex sitting next to it. *)
Goal forall v : word, v_addi v 4 = v_addi v 4.
Proof. intros v. wlit (v_addi v 4). wlits. reflexivity. Abort.
Goal forall v : word,
  (v_addi (Z_to_bv 64 5) 3, v_addi v 4) = (Z_to_bv 64 8, v_addi v 4).
Proof.
  intros v. wlits.
  lazymatch goal with |- (@BV _ _ _, _) = _ => idtac end.
  f_equal. bveq.
Abort.

(** The [stepw] address/value discharge scripts — the examples'
    standard store-obligation pattern (resolve the register
    projections, [sp_norm], then [reflexivity]/[f_equal; lia]/[bveq];
    the [bveq] fallback is closedness-guarded, so an OPEN obligation
    fails fast instead of reaching the vm). *)
End WithFP25.
Ltac stepw_addr :=
  getr_resolve; regupd_resolve; sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].
Ltac stepw_val :=
  getr_resolve; regupd_resolve; cbv beta; reduce_bv_eqb_ifs;
  first [ reflexivity | sp_norm; first [ reflexivity | f_equal; lia ] | bveq ].

(** [stepw_addr] for the put-style retry loops, whose spill addresses
    reach the obligation as [v_addi] of a register the chain has already
    pinned by an equation in the context: rewrite by those equations and
    fold the immediate away before running the [stepw_addr] script.
    Every name here is generic, so this belongs beside its weaker
    sibling rather than copied into each proof that needs it. *)
Ltac stepw_addr_hyps :=
  getr_resolve; regupd_resolve;
  repeat match goal with
  | H : Sem.reg_get ?R ?r = _ |- context [Sem.reg_get ?R ?r] => rewrite H
  end;
  imm_norm; rewrite ?v_addi_0;
  sp_norm;
  first [ reflexivity | f_equal; lia | bveq ].

Section WithFP27.
Context {fx : FPState}.

(** One machine STORE inside a chain, dispatched on the decoded width
    ([sd]/[sw]/[sh]/[sb] -> [step_sd_at]/[step_sw_at]/[step_sh_at]/
    [MmapSim.step_sb_at]) — the store analogue of [stepiv].  [aa]/[vv]
    are the pre-normalized store address and value ([sb] additionally
    pre-normalizes the stored byte to [Z_to_bv 8 (bv_unsigned vv)]);
    the address and value obligations get [stepw_addr]/[stepw_val]
    baked in; the [store_ok] obligation goes to the caller-supplied
    [oktac] ([StoreOk.solve_store_ok] cannot be named here — StoreOk
    imports this file). *)
End WithFP27.
Ltac stepw F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ2 _ _ _, _) =>
        eapply step_sh_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | stepw_addr | stepw_val
        | reflexivity | oktac ]
    end
  | step_simpl ].

(** The put-style retry loops' spill and reload: one [sd]/[ld] at an
    address the caller pre-normalizes, discharged through
    [stepw_addr_hyps].  [stepsd]'s [store_ok] obligation goes to the
    caller-supplied [oktac] for the same reason [stepw]'s does — StoreOk
    imports this file, so its solver cannot be named here — while
    [stepld] needs no such argument, taking only the caller's [readtac]
    for the [rdn] side condition. *)
Ltac stepsd F D aexp vexp vtac oktac :=
  step_intro;
  [ reflexivity
  | eapply step_sd_at with (a := aexp) (v := vexp);
    [ exact F | reflexivity | exact D | stepw_addr_hyps | vtac | oktac ]
  | step_simpl ].

Ltac stepld F D aexp vexp readtac :=
  step_intro;
  [ reflexivity
  | eapply step_ld with (bs := word_to_le_bytes 8 vexp) (v := vexp);
    [ exact F | reflexivity | exact D
    | match goal with |- rdn _ _ ?ad _ = _ =>
        replace ad with aexp by stepw_addr_hyps
      end; readtac
    | exact (bytes_le_to_Z_8 _) ]
  | step_simpl ].

Section WithFP28.
Context {fx : FPState}.

(** Prove the current (decidable) goal by a VM-checked cast of
    [eq_refl] via [bool_decide] — cheaper than [vm_compute;
    reflexivity], which normalizes the goal twice, and the only form
    that closes bv equations under vm (plain [vm_compute; reflexivity]
    gets stuck on the opaque [Z_to_bv] wf proofs).  Same idiom as the
    generated fetch/decode lemmas' [vm_refl]: the [Examples/*/*_code.v]
    headers alias [Ltac vm_refl := vm_refl_bv] after importing this
    file, and [gen-fd-lemmas] documents that alias.  This is
    the single source of truth for the idiom — keep the generator's
    docstring in sync if this body changes. *)
End WithFP28.
Ltac vm_refl_bv :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Section WithFP29.
Context {fx : FPState}.

(** Replace a CLOSED word-valued redex [p] (e.g. the fault address
    [v_addi (Z_to_bv 64 0) (bv_signed imm)]) with its vm-computed
    [Z_to_bv 64 z] literal.  This is the robust replacement for the
    fragile [rewrite v_addi_0_*] pattern: a [rewrite] cannot match a
    closed redex whose reduction needs conversion on a [bv_signed]
    literal (no pattern variable triggers it), while [replace ... by
    bveq] always can.  State per-image ROM facts (e.g. [*_none]
    unmapped-address facts) at the same [Z_to_bv 64 z] spelling so
    they apply directly afterwards.  Fails fast when [p] is open
    (the explicit [check_closed_term] call runs in tactic position, so
    a direct caller gets its error message rather than [vm_eval]'s
    failure surfacing as a match failure). *)
End WithFP29.
Ltac wlit_closed p :=
  check_closed_term p;
  let u := vm_eval (bv_unsigned p) in
  replace p with (Z_to_bv 64 u) by bveq.

Section WithFP30.
Context {fx : FPState}.

(** Sweep form of [wlit_closed]: normalize every CLOSED
    [v_addi]/[v_add]/[v_sub] redex in the goal to its [Z_to_bv 64 z]
    literal (open redexes are skipped; point [wlit_closed] at other
    shapes by hand).  Note this produces the [Z_to_bv] spelling, not
    the numeral-literal one [wlits] produces — use it for value/ROM
    positions, [wlits]/[norm_pc] for pc positions. *)
End WithFP30.
Ltac wlits_closed :=
  repeat match goal with
  | |- context [v_addi ?a ?b] => wlit_closed (v_addi a b)
  | |- context [v_add ?a ?b] => wlit_closed (v_add a b)
  | |- context [v_sub ?a ?b] => wlit_closed (v_sub a b)
  end.

Section WithFP32.
Context {fx : FPState}.

(** Wrapper for the [erewrite rdn_ext] call-site pattern: rewrites the
    (first) [rdn segs mem a k] in the goal to an evar memory,
    discharges the no-overflow side condition by [imm_norm; u_norm;
    lia], and pre-normalizes the pointwise premise so [lia] sees
    literal addresses ([intros x Hx; revert Hx; imm_norm; u_norm;
    intros Hx]).  Leaves two goals: (1) the rewritten main goal (close
    it with the ROM fact, instantiating the evar), then (2) the
    normalized pointwise premise [m1 x = ?m2 x] under the literal
    bounds hypothesis. *)
End WithFP32.
Ltac rdn_ext_lit :=
  erewrite rdn_ext;
    [ (* main goal: apply the ROM fact *)
    | imm_norm; u_norm; lia
    | let x := fresh "x" in
      let Hx := fresh "Hx" in
      intros x Hx; revert Hx; imm_norm; u_norm; intros Hx ].

Section WithFP33.
Context {fx : FPState}.

(* ######################################################################### *)
(* Consolidated shared lemmas                                                *)
(* ######################################################################### *)

(** A byte disequality against literal zero transfers to the [Z] level. *)
Lemma byte_nz_u : forall b : byte, b <> Z_to_bv 8 0 -> (bv_unsigned b <> 0)%Z.
Proof.
  intros b Hb Hc. apply Hb. apply bv_eq. rewrite Hc. reflexivity.
Qed.

(** [bv_unsigned] of a byte zero-extended into a word. *)
Lemma u_zext8 : forall b : byte,
  bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof.
  intro b. apply u_Z2bv; pose proof (u8_range b); lia.
Qed.

(** Truncating the zero-extended byte back to 8 bits recovers it. *)
Lemma zext8_byte : forall b : byte,
  Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (bv_unsigned b))) = b.
Proof.
  intro b. apply bv_eq.
  rewrite Z_to_bv_unsigned, u_zext8.
  apply bv_wrap_small. pose proof (u8_range b).
  change (bv_modulus 8) with 256%Z. lia.
Qed.

(** A byte-literal disequality transfers to the [Z] level. *)
Lemma byte_neq_lit_u : forall (b : byte) (z : Z), (0 <= z < 256)%Z ->
  b <> Z_to_bv 8 z -> (bv_unsigned b <> z)%Z.
Proof.
  intros b z Hz Hb Hc. apply Hb. apply bv_eq.
  rewrite Hc, Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Z.mod_small; [reflexivity |].
  change (bv_modulus 8) with 256%Z. lia.
Qed.

(** Two-register byte dispatch compares the zero-extended loaded byte
    against a zero-extended literal: reflect a byte-literal
    disequality into the [c_eq ... = false] the branch step needs. *)
Lemma c_eq_zext_lit_false : forall (b : byte) (z : Z), (0 <= z < 256)%Z ->
  b <> Z_to_bv 8 z ->
  c_eq (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 z) = false.
Proof.
  intros b z Hz Hb. unfold c_eq, bv_eqb. apply Z.eqb_neq.
  rewrite u_zext8, u_Z2bv by lia.
  exact (byte_neq_lit_u b z Hz Hb).
Qed.

(** [bv_unsigned] of an in-range [nat_to_word]. *)
Lemma u_ntw : forall n : nat, (Z.of_nat n < 2^64)%Z ->
  bv_unsigned (nat_to_word n) = Z.of_nat n.
Proof. intros n Hn. unfold nat_to_word. apply u_Z2bv; lia. Qed.

(** The wrapping word/nat offset add in the canonical [Z_to_bv] form
    (hypothesis-free: both sides wrap identically). *)
Lemma word_add_nat : forall (a : word) (n : nat),
  a + nat_to_word n = Z_to_bv 64 (bv_unsigned a + Z.of_nat n).
Proof.
  intros a n. apply bv_eq. unfold nat_to_word.
  rewrite bv_add_unsigned, !Z_to_bv_unsigned, bv_wrap_add_idemp_r.
  reflexivity.
Qed.

(** The wrapping add of [nat_to_word 0] is the identity
    (hypothesis-free).  NOTE: named [word_add_nat_0], not
    [word_add_0_r] — AllocSim exports a different [word_add_0_r]
    stated at [Z_to_bv 64 0]. *)
Lemma word_add_nat_0 : forall x : word, x + nat_to_word 0 = x.
Proof.
  intro x. apply bv_eq. rewrite word_add_nat.
  rewrite u_Z2bv by (pose proof (u64_range x); lia). lia.
Qed.

(** Loop-index steps over a symbolic base (both sides wrap). *)
Lemma word_add_nat_1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word m) 1 = a + nat_to_word (S m).
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Lemma word_add_nat_m1 : forall (a : word) (m : nat),
  v_addi (a + nat_to_word (S m)) (-1) = a + nat_to_word m.
Proof.
  intros a m. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(** [v_add] is commutative up to the wrap. *)
Lemma v_add_comm : forall x y : word, v_add x y = y + x.
Proof.
  intros x y. apply bv_eq.
  change (v_add x y) with (x + y).
  rewrite !bv_add_unsigned. f_equal. lia.
Qed.

(** A wrapping [v_add], with the wrapped value made explicit. *)
Lemma v_add_wrap : forall x y : word,
  (2^64 <= bv_unsigned x + bv_unsigned y)%Z ->
  v_add x y = Z_to_bv 64 (bv_unsigned x + bv_unsigned y - 2^64).
Proof.
  intros x y Hw. unfold v_add. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite <- (Z.mod_add (bv_unsigned x + bv_unsigned y - 2^64) 1 (2^64)) by lia.
  f_equal. lia.
Qed.

(** [sub x0, y]: two's-complement negation in the canonical form. *)
Lemma v_sub_0_neg : forall y : word,
  v_sub (Z_to_bv 64 0) y = Z_to_bv 64 (- bv_unsigned y).
Proof.
  intro y. unfold v_sub.
  change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
  f_equal.
Qed.

(** Unsigned value of a small negation. *)
Lemma u_neg_small : forall z : Z, (0 < z)%Z -> (z <= 2^64)%Z ->
  bv_unsigned (Z_to_bv 64 (- z)) = (2^64 - z)%Z.
Proof.
  intros z Hz0 Hz. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
  replace (- z)%Z with ((2^64 - z) + (-1) * 2^64)%Z by lia.
  rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

(** Incrementing a negative down-counter. *)
Lemma v_addi_neg_S : forall d : nat,
  v_addi (Z_to_bv 64 (- Z.of_nat (S d))) 1 = Z_to_bv 64 (- Z.of_nat d).
Proof.
  intro d. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(** C, the distance [create_elf_tables] (fs/binfmt_elf.c, Linux
    v6.18.46, commit 1f99e9ab748f) puts between the entry stack pointer
    and the top of AT_RANDOM, is the pointer vector plus at most 512
    fixed bytes: 29 auxv pairs at most (464), the three NULL/argc slots
    (24), [STACK_ALLOC]'s 16 and [STACK_ROUND]'s odd-item 8. *)
Lemma block_head_size_le : forall rseq argv envp,
  (Z.of_nat (block_head_size rseq argv envp)
   <= 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 512)%Z.
Proof.
  intros rseq argv envp.
  unfold block_head_size, block_items, auxv_size, auxv_count.
  pose proof (Nat.mod_upper_bound
                (length argv + length envp + 3) 2 ltac:(lia)).
  destruct rseq; lia.
Qed.

(** The entry stack pointer is below the stack VMA's end:
    [create_elf_tables] only ever subtracts from [bprm->p], which
    already sits [8 + L] below the end. *)
Lemma launch_sp_le_top : forall inp (top sp : word),
  valid_launch_sp top inp sp ->
  (bv_unsigned sp <= bv_unsigned top)%Z.
Proof.
  intros inp top sp [_ [_ Hhi]].
  unfold launch_sp_hi, align_down16 in Hhi.
  pose proof (Nat2Z.is_nonneg
    (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  pose proof (Nat2Z.is_nonneg
    (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  pose proof (Z.mod_pos_bound
    (bv_unsigned top - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp))) 16 ltac:(lia)).
  lia.
Qed.

(** How far below the stack VMA's end the entry stack pointer can sit.
    [Run.launch_sp_lo] is [align_down16 (top - 8 - L - 4095) - C], and
    [align_down16] drops at most 15, so the distance is at most
    [L + C + 4118].  [Run.valid_launch] caps [L + 8 * (argc + envc)] at
    [Run.e2big_limit] (2 MiB) and [block_head_size_le] caps [C] at
    [8 * (argc + envc) + 512], so the sum is at most 2101782 whatever
    the input. *)
Lemma launch_top_minus_sp : forall inp (top sp : word),
  valid_launch inp ->
  valid_launch_sp top inp sp ->
  (bv_unsigned top - bv_unsigned sp <= 2101782)%Z.
Proof.
  intros inp top sp [_ Hb] [_ [Hlo _]].
  unfold launch_bytes, e2big_limit in Hb.
  unfold launch_sp_lo, align_down16 in Hlo.
  pose proof (block_head_size_le (kb_rseq (in_kernel inp))
                (in_argv inp) (in_envp inp)).
  pose proof (Z.mod_pos_bound
    (bv_unsigned top - 8
     - Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp)
                                     (in_execfn inp))
     - 4095) 16 ltac:(lia)).
  lia.
Qed.

(** Upper bound on the initial stack image (feeds every read lemma's
    no-overflow side condition).

    Derived rather than computed, and now from the LAUNCH rather than
    from [valid_argv]/[valid_envp]: the image is exactly the block
    between [sp] and the stack VMA's end
    ([PropExec.length_entry_stack_image_launch]), and
    [launch_top_minus_sp] bounds that distance.  The older derivation
    went through [PropExec.build_stack_bytes_within_span] and
    [Run.entry_stack_span_bound]; that span counted neither the exec
    file name nor [arch_align_stack]'s pad, so it is no longer an upper
    bound on the block and the lemma behind it is retired. *)
Lemma bsb_bound : forall v inp mbase ph entry (sp brk : word) draw,
  valid_launch inp ->
  entry_launch_ok_va v (mkEntry sp brk mbase draw) inp ->
  (Z.of_nat (length (entry_stack_image inp mbase ph entry sp draw))
   <= 2101782)%Z.
Proof.
  intros v inp mbase ph entry sp brk draw Hvl Hlau.
  rewrite (length_entry_stack_image_launch v inp mbase ph entry sp brk draw
             Hlau).
  destruct Hlau as (_ & Hsp & _).
  exact (launch_top_minus_sp inp (ed_top draw) sp Hvl Hsp).
Qed.

(** A store range at/above the ends of both segments of a two-segment
    image passes the read-only-avoidance check (per-image
    [*_avoids_ro] facts specialize the two [Z.ltb] hypotheses). *)
Lemma range_avoids_two : forall (s0 s1 : Segment) (a n : Z),
  Z.ltb a (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)) = false ->
  Z.ltb a (Z.of_N (seg_base s1) + Z.of_N (seg_size s1)) = false ->
  range_avoids_ro_segs [s0; s1] a n = true.
Proof.
  intros s0 s1 a n H0 H1. unfold range_avoids_ro_segs. cbn [forallb].
  rewrite H0, H1. rewrite !andb_false_r. cbn [negb]. rewrite !orb_true_r.
  reflexivity.
Qed.

(** ** Avoiding the read-only segments, for any number of segments

    [range_avoids_two] above is fixed at two segments.  Each example
    proves the same fact about its own image, and the hand-rolled proof
    names every segment explicitly — so it has to be edited by hand
    whenever the segment COUNT changes (for example, gcc can give
    .eh_frame a LOAD segment of its own, which takes an image from three
    segments to four).

    [range_avoids_ro_above] states it once, keyed off a single bound:
    if every read-only segment ends at or below [data_base], then any
    range starting at or above [data_base] avoids all of them —
    whatever the segment count.  The premise is closed by [vm_compute]
    on a concrete image, so the per-example lemma becomes one line:

      Lemma source_avoids_ro : forall a n, (0x13000 <= bv_unsigned a)%Z ->
        range_avoids_ro_segs source_segs (bv_unsigned a) n = true.
      Proof.
        intros a n Ha.
        apply range_avoids_ro_above with (data_base := 0x13000%Z);
          [vm_compute; reflexivity | exact Ha].
      Qed.

    Note the range's LENGTH is irrelevant, as it is for
    [range_avoids_two]: a range that starts above every read-only
    segment cannot re-enter one by being long, because the segments lie
    below it. *)
Definition ro_segs_below (segs : list Segment) (data_base : Z) : bool :=
  forallb (fun seg =>
             seg_writable seg
             || Z.leb (Z.of_N (seg_base seg) + Z.of_N (seg_size seg)) data_base)
          segs.

Lemma range_avoids_ro_above : forall (segs : list Segment) (data_base addr n : Z),
  ro_segs_below segs data_base = true ->
  (data_base <= addr)%Z ->
  range_avoids_ro_segs segs addr n = true.
Proof.
  intros segs data_base addr n Hbelow Haddr.
  unfold ro_segs_below in Hbelow. unfold range_avoids_ro_segs.
  rewrite forallb_forall in *. intros seg Hin.
  specialize (Hbelow seg Hin).
  destruct (seg_writable seg) eqn:W; cbn [orb] in *; [reflexivity|].
  apply Z.leb_le in Hbelow.
  apply negb_true_iff. apply andb_false_iff. right.
  apply Z.ltb_ge. lia.
Qed.

(* ######################################################################### *)
(* Smoke tests: the dispatch arms actually fire                              *)
(* ######################################################################### *)

(** Each test drives [stepi]/[stepiv]/[stepw]/[stepj]/[stepjr] over ONE
    concrete instruction encoding.  [segs]/[regs]/[mem] stay abstract;
    the fetch fact is a hypothesis; the decode fact is proved by vm on
    the encoding — so a test fails if the encoding, the dispatch arm,
    the lemma's argument count, or the post-step normalization is
    wrong.  The pc is a closed literal ([norm_pc] vm-computes it: an
    OPEN pc would be the open-bv trap).  All tests [Abort]: the point
    is that the tactic runs, not the statement. *)

Section DispatchSmoke.
  Variable segs : list Segment.
  Variable regs : bvmap 5 word.
  Variable mem rom : word -> option byte.

  (** Scaffold: consume the fetch hypothesis, prove the decode fact by
      vm on the concrete encoding, take one [stepi], close the chain. *)
  Ltac smoke enc sh :=
    let F := fresh "F" in
    intro F;
    let D := fresh "D" in
    assert (D : decode_any enc = Some (sh, 4%Z)) by vm_refl_bv;
    eexists; stepi F D; apply mst_refl.

  (* slti a0,a0,1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00152513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00152513 : bv 32) (OpImm ALU_SLT 10 10 1). Abort.

  (* srai a0,a0,1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40155513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40155513 : bv 32) (ShiftImm ALU_SRA 10 10 1). Abort.

  (* and a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B57533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B57533 : bv 32) (Op ALU_AND 10 10 11). Abort.

  (* or a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B56533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B56533 : bv 32) (Op ALU_OR 10 10 11). Abort.

  (* xor a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B54533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B54533 : bv 32) (Op ALU_XOR 10 10 11). Abort.

  (* sll a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B51533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B51533 : bv 32) (Op ALU_SLL 10 10 11). Abort.

  (* srl a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B55533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B55533 : bv 32) (Op ALU_SRL 10 10 11). Abort.

  (* sra a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40B55533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40B55533 : bv 32) (Op ALU_SRA 10 10 11). Abort.

  (* slt a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B52533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B52533 : bv 32) (Op ALU_SLT 10 10 11). Abort.

  (* sltu a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B53533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B53533 : bv 32) (Op ALU_SLTU 10 10 11). Abort.

  (* addw a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5053B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5053B : bv 32) (Op32 ALU_ADD 10 10 11). Abort.

  (* sllw a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5153B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5153B : bv 32) (Op32 ALU_SLL 10 10 11). Abort.

  (* srlw a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x00B5553B : bv 32) (Op32 ALU_SRL 10 10 11). Abort.

  (* sraw a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x40B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x40B5553B : bv 32) (Op32 ALU_SRA 10 10 11). Abort.

  (* addiw a0,a0,1 — regression test: if this arm's [exact] misses
     an argument slot, [stepi] FAILS on every OpImm32 decode (the
     failure happens inside the selected [lazymatch] arm, which does
     not fall through to [stepi_search]). *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015051B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015051B : bv 32) (OpImm32 10 10 1). Abort.

  (* slliw a0,a0,1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015151B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015151B : bv 32) (ShiftImm32 ALU_SLL 10 10 1). Abort.

  (* srliw a0,a0,1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0015551B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x0015551B : bv 32) (ShiftImm32 ALU_SRL 10 10 1). Abort.

  (* sraiw a0,a0,1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x4015551B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x4015551B : bv 32) (ShiftImm32 ALU_SRA 10 10 1). Abort.

  (* mulh a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B51533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B51533 : bv 32) (Mul M_MULH 10 10 11). Abort.

  (* mulhsu a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B52533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B52533 : bv 32) (Mul M_MULHSU 10 10 11). Abort.

  (* mulhu a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B53533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B53533 : bv 32) (Mul M_MULHU 10 10 11). Abort.

  (* div a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B54533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B54533 : bv 32) (Mul M_DIV 10 10 11). Abort.

  (* rem a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B56533 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B56533 : bv 32) (Mul M_REM 10 10 11). Abort.

  (* mulw a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5053B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5053B : bv 32) (Mul32 M_MUL 10 10 11). Abort.

  (* divw a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5453B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5453B : bv 32) (Mul32 M_DIV 10 10 11). Abort.

  (* divuw a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5553B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5553B : bv 32) (Mul32 M_DIVU 10 10 11). Abort.

  (* remw a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5653B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5653B : bv 32) (Mul32 M_REM 10 10 11). Abort.

  (* remuw a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B5753B : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof. smoke (0x02B5753B : bv 32) (Mul32 M_REMU 10 10 11). Abort.

  (* divu a0,a0,a1 — the nonzero-divisor premise is picked up from the
     context by the arm's [assumption]. *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B55533 : bv 32) ->
    (bv_unsigned (getr regs 11) <> 0)%Z ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F NZ.
    assert (D : decode_any (0x02B55533 : bv 32)
                = Some (Mul M_DIVU 10 10 11, 4%Z)) by vm_refl_bv.
    eexists. stepi F D. apply mst_refl.
  Abort.

  (* remu a0,a0,a1 *)
  Goal fetch_word segs (0x10000 : word) = Some (0x02B57533 : bv 32) ->
    (bv_unsigned (getr regs 11) <> 0)%Z ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F NZ.
    assert (D : decode_any (0x02B57533 : bv 32)
                = Some (Mul M_REMU 10 10 11, 4%Z)) by vm_refl_bv.
    eexists. stepi F D. apply mst_refl.
  Abort.

  (* [stepiv] dispatch: slli a0,a0,1 (new [step_slli_at]). *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00151513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x00151513 : bv 32)
                = Some (ShiftImm ALU_SLL 10 10 1, 4%Z)) by vm_refl_bv.
    eexists. stepiv F D (v_slli (getr regs 10) 1) ltac:(reflexivity).
    apply mst_refl.
  Abort.

  (* [stepiv] dispatch: andi a0,a0,1 (new [step_andi_at]). *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00157513 : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x00157513 : bv 32)
                = Some (OpImm ALU_AND 10 10 1, 4%Z)) by vm_refl_bv.
    eexists. stepiv F D (v_andi (getr regs 10) 1) ltac:(reflexivity).
    apply mst_refl.
  Abort.

  (* [stepw]: sd a0,0(sp) *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A13023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 8%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A13023 : bv 32)
                = Some (Store SZ8 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [stepw]: sw a0,0(sp) *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A12023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 4%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A12023 : bv 32)
                = Some (Store SZ4 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [stepw]: sh a0,0(sp) *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A11023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 2%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A11023 : bv 32)
                = Some (Store SZ2 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [stepw]: sb a0,0(sp) *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00A10023 : bv 32) ->
    RiscvSemantics.store_ok segs mem (v_addi (getr regs 2) 0) 1%nat = true ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F OK.
    assert (D : decode_any (0x00A10023 : bv 32)
                = Some (Store SZ1 2 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepw F D (v_addi (getr regs 2) 0) (getr regs 10) ltac:(exact OK).
    apply mst_refl.
  Abort.

  (* [stepj]: jal x0,+8 (the no-link form). *)
  Goal fetch_word segs (0x10000 : word) = Some (0x0080006F : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x0080006F : bv 32)
                = Some (Jal 0 8, 4%Z)) by vm_refl_bv.
    eexists. stepj F D. apply mst_refl.
  Abort.

  (* [stepj]: jal ra,+8 (the LINKING form). *)
  Goal fetch_word segs (0x10000 : word) = Some (0x008000EF : bv 32) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intro F.
    assert (D : decode_any (0x008000EF : bv 32)
                = Some (Jal 1 8, 4%Z)) by vm_refl_bv.
    eexists. stepj F D. apply mst_refl.
  Abort.

  (* [stepjr]: jalr x0,0(ra) — ret, target from a resolved register. *)
  Goal fetch_word segs (0x10000 : word) = Some (0x00008067 : bv 32) ->
    getr regs 1 = (0x20000 : word) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F R.
    assert (D : decode_any (0x00008067 : bv 32)
                = Some (Jalr 0 1 0, 4%Z)) by vm_refl_bv.
    eexists. stepjr F D (0x20000 : word) ltac:(exact R).
    apply mst_refl.
  Abort.

  (* [stepjr]: jalr ra,0(a0) — a linking call through a register. *)
  Goal fetch_word segs (0x10000 : word) = Some (0x000500E7 : bv 32) ->
    getr regs 10 = (0x20000 : word) ->
    exists st', msteps segs (mkst regs (0x10000 : word) mem rom) st'.
  Proof.
    intros F R.
    assert (D : decode_any (0x000500E7 : bv 32)
                = Some (Jalr 1 10 0, 4%Z)) by vm_refl_bv.
    eexists. stepjr F D (0x20000 : word) ltac:(exact R).
    apply mst_refl.
  Abort.

End DispatchSmoke.
End WithFP33.
