(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition bsegs := AsanUbsan.M.loaded_segments.
Definition B_SHBASE : Z := 2147450880.

Definition b_is_shadow_addr (a : saddr) : bool :=
  (a_off a =? B_SHBASE) && match a_base a with EAlu ALU_SRL _ (ELit 3) => true | _ => false end.
Fixpoint b_last_sh_req (scs : list sidecond) (acc : option saddr) : option saddr :=
  match scs with
  | [] => acc
  | SCReadBase a 1 _ _ :: t => if b_is_shadow_addr a then b_last_sh_req t (Some a) else b_last_sh_req t acc
  | _ :: t => b_last_sh_req t acc
  end.
Fixpoint kn_fixB (fuel : nat) (sfuel : nat) (stops : list Z) (scr : scripts) (pc : Z) (sr : list expr)
         (kn : list kentry) (nx : N) : list kentry :=
  match fuel with
  | O => kn
  | S f =>
      let '(_, scs, _) := sym_exec bsegs sfuel true stops scr (SS pc sr [] kn nx) [] in
      match b_last_sh_req scs None with
      | None => kn
      | Some a => kn_fixB f sfuel stops scr pc sr (kn ++ [KWord a 1 (ELit 0)]) nx
      end
  end.
