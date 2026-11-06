(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec AxSymExec3 AxSymExec3B AsanPlanCore LibSym SegRun SegPlan.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations. Import AX2. Import AX2B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SGA.
Section WithImage.
Variable segs : list Segment. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable IT : itab.
Variable x_cpy x_set x_len ro_lo ro_hi : Z.
Variable BFUEL : nat.
Variable STOPS : list Z.
Variable ENDS : list Z.        (* [comment removed for export] *)
Variable A : APC.atable.             (* [comment removed for export] *)
Variable F : list SGP.region.

Definition STEP (st : SR.sstep) := SGP.step1 segs IT x_cpy x_set x_len ro_lo ro_hi BFUEL F st.
Definition is_lit (e : expr) : bool := match e with ELit _ => true | _ => false end.
Inductive aitem := AStep (st : SR.sstep) | ACopyX | AFillX.
Fixpoint mkplan (l : list aitem) (tail : SGP.splan) : SGP.splan :=
  match l with
  | [] => tail
  | AStep st :: r => SGP.PStep st (mkplan r tail)
  | ACopyX :: r => SGP.PCopyX (mkplan r tail)
  | AFillX :: r => SGP.PFillX (mkplan r tail)
  end.
(* [comment removed for export] *)
Definition special (ss : sym_state) : option (aitem * sym_state) :=
  if Z.eqb (s_pc ss) x_cpy then
    (if is_lit (SR.reg ss 12) then
       match STEP SR.SCopy ss with Some s' => Some (AStep SR.SCopy, s') | None => None end
     else match SGP.copyx x_cpy A F ss with Some s' => Some (ACopyX, s') | None => None end)
  else if Z.eqb (s_pc ss) x_set then
    (if is_lit (SR.reg ss 12) then
       match STEP SR.SFill ss with Some s' => Some (AStep SR.SFill, s') | None => None end
     else match SGP.fillx x_set F ss with Some s' => Some (AFillX, s') | None => None end)
  else match itab_lookup IT (s_pc ss) with
       | Some (Instr.FStore Instr.FMT_D _ _ _) => match STEP (SR.SFsdSeq 32) ss with Some s' => Some (AStep (SR.SFsdSeq 32), s') | None => None end
       | Some (Instr.FLoad Instr.FMT_D _ _ _) => match STEP (SR.SFldSeq 32) ss with Some s' => Some (AStep (SR.SFldSeq 32), s') | None => None end
       | _ => None
       end.
Fixpoint auto (n : nat) (ss : sym_state) : list aitem * (Z * sym_state) :=
  match n with
  | O => ([], (90, ss))
  | S m =>
    if existsb (Z.eqb (s_pc ss)) ENDS then ([], (93, ss)) else
    match special ss with
    | Some (it, s') => let '(l, r) := auto m s' in (it :: l, r)
    | None =>
        match STEP (SR.SBlock STOPS) ss with
        | Some ss' =>
            if negb (Z.eqb (s_pc ss') (s_pc ss)) then let '(l, r) := auto m ss' in (AStep (SR.SBlock STOPS) :: l, r)
            else ([], (91, ss'))
        | None => ([], (92, ss))
        end
    end
  end.
End WithImage.
End SGA.
