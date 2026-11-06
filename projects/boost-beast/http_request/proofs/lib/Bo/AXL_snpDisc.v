(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_beast.http_request.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Frame StreamSim SymExec SymExec2X SymExec2SoundX SymRunX SymPackX RefMemcpyLib AgentLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Import SX2. Import SX2S.

Section Disc.
  Variable segs : list Segment.
  Variable E0 : env.
  Variable stops : list Z.

  Definition disc_step (fuel : nat) (first : bool) (ss : sym_state) (acc : list sidecond)
    : sym_state * list sidecond * option bool :=
    let r := sym_exec segs fuel first stops (SCR [] [] []) ss acc in
    let ss' := fst (fst r) in
    match fetch_word segs (Z_to_bv 64 (s_pc ss')) with
    | Some w =>
        match decode_any w with
        | Some (Branch c rs1 rs2 _, _) =>
            if existsb (Z.eqb (s_pc ss')) stops then (ss', snd (fst r), None) else
            let a := sr_get (s_regs ss') rs1 in let b := sr_get (s_regs ss') rs2 in
            (ss', snd (fst r), Some (branch_taken c (edenot E0 a) (edenot E0 b)))
        | _ => (ss', snd (fst r), None)
        end
    | None => (ss', snd (fst r), None)
    end.

  Fixpoint discover (rounds : nat) (fuel : nat) (first : bool) (ss : sym_state) (acc : list sidecond) (dirs : list (Z * bool))
    : list (Z * bool) * sym_state * list sidecond * nat :=
    match rounds with
    | O => (dirs, ss, acc, O)
    | S k =>
        match disc_step fuel first ss acc with
        | (ss', acc', None) => (dirs, ss', acc', k)
        | (ss', acc', Some t) =>
            let r := sym_exec segs 1%nat true stops (SCR [t] [] []) ss' acc' in
            discover k fuel true (fst (fst r)) (snd (fst r)) (dirs ++ [(s_pc ss', t)])
        end
    end.
End Disc.
