(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr Decode DecodeC.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require SymExec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import SymExec2.SX2.

Section WithSegs.
Variable segs : list Segment.
Variable t : SymExec3.SX2.itab.

Fixpoint sym_execI (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                   (ss : sym_state) (acc : list sidecond)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => (ss, acc, scr)
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (ss, acc, scr) else
      match SymExec3.SX2.itab_lookup t (s_pc ss) with
      | Some i =>
          match sym_step segs i ss scr with
          | SOk ss' scs scr' => sym_execI f false stops scr' ss' (sc_add scs acc)
          | SStop => (ss, acc, scr)
          end
      | None =>
          match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
          | None => (ss, acc, scr)
          | Some w =>
              if is_ecall w then (ss, acc, scr) else
              match decode_any w with
              | None => (ss, acc, scr)
              | Some (i, sz) =>
                  if negb (Z.eqb sz 4) then (ss, acc, scr) else
                  match sym_step segs i ss scr with
                  | SOk ss' scs scr' => sym_execI f false stops scr' ss' (sc_add scs acc)
                  | SStop => (ss, acc, scr)
                  end
              end
          end
      end
  end.

Theorem sym_execI_eq : SymExec3.SX2.itab_sound segs t ->
  forall fuel first stops scr ss acc,
  sym_execI fuel first stops scr ss acc = sym_exec segs fuel first stops scr ss acc.
Proof.
  intros Ht. induction fuel as [|f IH]; intros first stops scr ss acc; [reflexivity|].
  cbn [sym_execI sym_exec].
  destruct (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool; [reflexivity|].
  destruct (SymExec3.SX2.itab_lookup t (s_pc ss)) as [i|] eqn:L.
  - pose proof (Ht _ _ L) as E. unfold SymExec3.SX2.itab_entry in E.
    destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|discriminate].
    destruct (is_ecall w); [discriminate|].
    destruct (decode_any w) as [[i' sz]|]; [|discriminate].
    destruct (Z.eqb sz 4); [|discriminate]. injection E as ->. cbn [negb].
    destruct (sym_step segs i ss scr) as [ss' scs scr'|]; [apply IH|reflexivity].
  - destruct (fetch_word segs (Z_to_bv 64 (s_pc ss))) as [w|]; [|reflexivity].
    destruct (is_ecall w); [reflexivity|].
    destruct (decode_any w) as [[i' sz]|]; [|reflexivity].
    destruct (negb (Z.eqb sz 4)); [reflexivity|].
    destruct (sym_step segs i' ss scr) as [ss' scs scr'|]; [apply IH|reflexivity].
Qed.
End WithSegs.
