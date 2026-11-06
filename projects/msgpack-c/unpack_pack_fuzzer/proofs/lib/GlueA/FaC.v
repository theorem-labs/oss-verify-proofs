(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module FaC.
Definition ZC_TOP : w64 := wlit 211106232532991%uint63.

Definition in_band (a : w64) : bool := wleu ActrB.ZC_BASE a && wleu a ZC_TOP.

Definition band_dec (fs : list fact) (l : sv) : option bool :=
  match l with
  | VL a => Some (in_band a)
  | _ => if known_leu fs (VL ActrB.ZC_BASE) l && known_leu fs l (VL ZC_TOP) then Some true
         else if known_ltu fs l (VL ActrB.ZC_BASE) || known_ltu fs (VL ZC_TOP) l then Some false
         else None
  end.

Fixpoint cr_free (fs : list fact) (n : nat) (ws : list sv) : bool :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      match kd with
      | VL k0 => (if weqb k0 wzero then
                    match sz with
                    | VL z => if weqb z wzero then match band_dec fs l with Some false => true | _ => false end else true
                    | _ => false
                    end
                  else true) && cr_free fs n' ws'
      | _ => false
      end
  | _, _ => true
  end.

Fixpoint pay (fs : list fact) (c : int) (n : nat) (ws : list sv) : option (list sv) :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      match kd with
      | VL k0 =>
          if weqb k0 wzero then
            match sz with
            | VL z =>
                if weqb z wzero then
                  match band_dec fs l with
                  | Some true => if known_leu fs (VL (wadd ActrB.ZC_BASE (wlit c))) l && cr_free fs n' ws'
                                 then Some (sv_alu ALU_SUB l (VL (wlit c)) :: sz :: kd :: ws') else None
                  | Some false => match pay fs c n' ws' with Some ws2 => Some (l :: sz :: kd :: ws2) | None => None end
                  | None => None
                  end
                else match pay fs c n' ws' with Some ws2 => Some (l :: sz :: kd :: ws2) | None => None end
            | _ => None
            end
          else match pay fs c n' ws' with Some ws2 => Some (l :: sz :: kd :: ws2) | None => None end
      | _ => None
      end
  | _, _ => None
  end.
Definition heap_pay (fs : list fact) (args : list sv) (c : int) : option (list sv) :=
  match heap_nwin args, args with
  | Some n, VL md :: a :: VL nw :: rest =>
      match pay fs c n (firstn (3 * n) rest) with
      | Some ws => Some (VL md :: a :: VL nw :: ws ++ skipn (3 * n) rest)
      | None => None
      end
  | _, _ => None
  end.

Section WithSegs.
Variable segs : list Segment.

Fixpoint first_dead (n : nat) (ws : list sv) (st : sstate) : option int :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      match l with
      | VP kf z => if sv_eqb kd (VL ActrB.K_FRAME) && (match ActrB.frame_status segs st l with ActrB.FDead => true | _ => false end)
                   then Some kf else first_dead n' ws' st
      | _ => first_dead n' ws' st
      end
  | _, _ => None
  end.

Definition abandon_one (st : sstate) : option sstate :=
  match s_resv st, ActrA.aheap_windows st with
  | RNone, Some (hargs, wl) =>
      match heap_nwin hargs, hargs with
      | Some n, VL md :: a :: VL nw :: rest =>
          match first_dead n (firstn (3 * n) rest) st with
          | Some kf =>
              match ActrB.find_twin (s_facts st) kf, heap_find_window hargs (VP kf wzero) with
              | Some shf, Some (_, len, kd) =>
                  match IMap.find shf (s_regs st) with
                  | Some rsh =>
                      if fresh_ok st && sv_eqb kd (VL ActrB.K_FRAME)
                         && ActrA.afree_ok_k ActrB.K_FRAME ActrB.K_FTWIN st wl kf shf
                         && ActrA.stack_room_g st 0%uint63 && ActrA.sp_floor_ok st hargs
                         && PrimInt63.eqb (rg_lo rsh) 0%uint63
                         && match DefsA.CtrA.win_lookup wl shf with Some (lent, _) => known_eq (s_facts st) (rg_hi rsh) lent | None => false end
                      then
                        match ActrB.heap_del_window_k hargs (VP kf wzero) ActrB.K_FRAME with
                        | Some h1 =>
                            match ActrB.heap_del_window_k h1 (VP shf wzero) ActrB.K_FTWIN with
                            | Some h2 =>
                                match heap_pay (s_facts st) h2 1%uint63 with
                                | Some h3 => Some (set_ops (setregs st (IMap.remove shf (IMap.remove kf (s_regs st)))) (set_op HEAP_ID h3 (s_ops st)))
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                      else None
                  | None => None
                  end
              | _, _ => None
              end
          | None => None
          end
      | _, _ => None
      end
  | _, _ => None
  end.

Fixpoint abandon_loop (fuel : nat) (st : sstate) (cnt : nat) : sstate * nat :=
  match fuel with
  | O => (st, cnt)
  | S f => match abandon_one st with
           | Some st' => abandon_loop f st' (S cnt)
           | None => (st, cnt)
           end
  end.

Definition burn (c : int) (st : sstate) : option sstate :=
  match s_resv st, ActrA.aheap_windows st with
  | RNone, Some (hargs, wl) =>
      if fresh_ok st && ActrA.stack_room_g st 0%uint63 && ActrA.sp_floor_ok st hargs then
        match heap_pay (s_facts st) hargs c with
        | Some h' => Some (set_ops st (set_op HEAP_ID h' (s_ops st)))
        | None => None
        end
      else None
  | _, _ => None
  end.

Definition frame_abandon_apply (st : sstate) : option (list sstate) :=
  let '(st1, cnt) := abandon_loop 16 st 0 in
  if Nat.eqb cnt 0 then None else
  if Nat.eqb cnt 16 then Some [st1] else
  match burn (of_Z (Z.of_nat (16 - cnt))) st1 with
  | Some st2 => Some [st2]
  | None => None
  end.
Definition frame_abandon_c (pc : int) : contract := Contract pc frame_abandon_apply.

Definition settle_apply (st : sstate) : option (list sstate) :=
  let '(st1, cnt) := abandon_loop 16 st 0 in
  if Nat.eqb cnt 16 then Some [st1] else
  match burn (of_Z (Z.of_nat (16 - cnt))) st1 with
  | Some st2 => Some [st2]
  | None => None
  end.
Definition settle_c (pc : int) : contract := Contract pc settle_apply.
End WithSegs.
End FaC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import Actr.TwinB.
Import ActrB.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module FaC.
Definition ZC_TOP : w64 := wlit 211106232532991%uint63.

Definition in_band (a : w64) : bool := wleu ActrB.TwinB.ActrB.ZC_BASE a && wleu a ZC_TOP.

Definition band_dec (fs : list fact) (l : sv) : option bool :=
  match l with
  | VL a => Some (in_band a)
  | _ => if known_leu fs (VL ActrB.TwinB.ActrB.ZC_BASE) l && known_leu fs l (VL ZC_TOP) then Some true
         else if known_ltu fs l (VL ActrB.TwinB.ActrB.ZC_BASE) || known_ltu fs (VL ZC_TOP) l then Some false
         else None
  end.

Fixpoint cr_free (fs : list fact) (n : nat) (ws : list sv) : bool :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      match kd with
      | VL k0 => (if weqb k0 wzero then
                    match sz with
                    | VL z => if weqb z wzero then match band_dec fs l with Some false => true | _ => false end else true
                    | _ => false
                    end
                  else true) && cr_free fs n' ws'
      | _ => false
      end
  | _, _ => true
  end.

Fixpoint pay (fs : list fact) (c : int) (n : nat) (ws : list sv) : option (list sv) :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      match kd with
      | VL k0 =>
          if weqb k0 wzero then
            match sz with
            | VL z =>
                if weqb z wzero then
                  match band_dec fs l with
                  | Some true => if known_leu fs (VL (wadd ActrB.TwinB.ActrB.ZC_BASE (wlit c))) l && cr_free fs n' ws'
                                 then Some (sv_alu ALU_SUB l (VL (wlit c)) :: sz :: kd :: ws') else None
                  | Some false => match pay fs c n' ws' with Some ws2 => Some (l :: sz :: kd :: ws2) | None => None end
                  | None => None
                  end
                else match pay fs c n' ws' with Some ws2 => Some (l :: sz :: kd :: ws2) | None => None end
            | _ => None
            end
          else match pay fs c n' ws' with Some ws2 => Some (l :: sz :: kd :: ws2) | None => None end
      | _ => None
      end
  | _, _ => None
  end.
Definition heap_pay (fs : list fact) (args : list sv) (c : int) : option (list sv) :=
  match heap_nwin args, args with
  | Some n, VL md :: a :: VL nw :: rest =>
      match pay fs c n (firstn (3 * n) rest) with
      | Some ws => Some (VL md :: a :: VL nw :: ws ++ skipn (3 * n) rest)
      | None => None
      end
  | _, _ => None
  end.

Section WithSegs.
Variable segs : list Segment.

Fixpoint first_dead (n : nat) (ws : list sv) (st : sstate) : option int :=
  match n, ws with
  | S n', l :: sz :: kd :: ws' =>
      match l with
      | VP kf z => if sv_eqb kd (VL ActrB.TwinB.ActrB.K_FRAME) && (match ActrB.TwinB.ActrB.frame_status segs st l with ActrB.TwinB.ActrB.FDead => true | _ => false end)
                   then Some kf else first_dead n' ws' st
      | _ => first_dead n' ws' st
      end
  | _, _ => None
  end.

Definition abandon_one (st : sstate) : option sstate :=
  match s_resv st, ActrA.aheap_windows st with
  | RNone, Some (hargs, wl) =>
      match heap_nwin hargs, hargs with
      | Some n, VL md :: a :: VL nw :: rest =>
          match first_dead n (firstn (3 * n) rest) st with
          | Some kf =>
              match ActrB.TwinB.ActrB.find_twin (s_facts st) kf, heap_find_window hargs (VP kf wzero) with
              | Some shf, Some (_, len, kd) =>
                  match IMap.find shf (s_regs st) with
                  | Some rsh =>
                      if fresh_ok st && sv_eqb kd (VL ActrB.TwinB.ActrB.K_FRAME)
                         && ActrA.afree_ok_k ActrB.TwinB.ActrB.K_FRAME ActrB.TwinB.ActrB.K_FTWIN st wl kf shf
                         && ActrA.stack_room_g st 0%uint63 && ActrA.sp_floor_ok st hargs
                         && PrimInt63.eqb (rg_lo rsh) 0%uint63
                         && match DefsA.CtrA.win_lookup wl shf with Some (lent, _) => known_eq (s_facts st) (rg_hi rsh) lent | None => false end
                      then
                        match ActrB.TwinB.ActrB.heap_del_window_k hargs (VP kf wzero) ActrB.TwinB.ActrB.K_FRAME with
                        | Some h1 =>
                            match ActrB.TwinB.ActrB.heap_del_window_k h1 (VP shf wzero) ActrB.TwinB.ActrB.K_FTWIN with
                            | Some h2 =>
                                match heap_pay (s_facts st) h2 1%uint63 with
                                | Some h3 => Some (set_ops (setregs st (IMap.remove shf (IMap.remove kf (s_regs st)))) (set_op HEAP_ID h3 (s_ops st)))
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                      else None
                  | None => None
                  end
              | _, _ => None
              end
          | None => None
          end
      | _, _ => None
      end
  | _, _ => None
  end.

Fixpoint abandon_loop (fuel : nat) (st : sstate) (cnt : nat) : sstate * nat :=
  match fuel with
  | O => (st, cnt)
  | S f => match abandon_one st with
           | Some st' => abandon_loop f st' (S cnt)
           | None => (st, cnt)
           end
  end.

Definition burn (c : int) (st : sstate) : option sstate :=
  match s_resv st, ActrA.aheap_windows st with
  | RNone, Some (hargs, wl) =>
      if fresh_ok st && ActrA.stack_room_g st 0%uint63 && ActrA.sp_floor_ok st hargs then
        match heap_pay (s_facts st) hargs c with
        | Some h' => Some (set_ops st (set_op HEAP_ID h' (s_ops st)))
        | None => None
        end
      else None
  | _, _ => None
  end.

Definition frame_abandon_apply (st : sstate) : option (list sstate) :=
  let '(st1, cnt) := abandon_loop 16 st 0 in
  if Nat.eqb cnt 0 then None else
  if Nat.eqb cnt 16 then Some [st1] else
  match burn (of_Z (Z.of_nat (16 - cnt))) st1 with
  | Some st2 => Some [st2]
  | None => None
  end.
Definition frame_abandon_c (pc : int) : contract := Contract pc frame_abandon_apply.

Definition settle_apply (st : sstate) : option (list sstate) :=
  let '(st1, cnt) := abandon_loop 16 st 0 in
  if Nat.eqb cnt 16 then Some [st1] else
  match burn (of_Z (Z.of_nat (16 - cnt))) st1 with
  | Some st2 => Some [st2]
  | None => None
  end.
Definition settle_c (pc : int) : contract := Contract pc settle_apply.
End WithSegs.
End FaC.
End TwinB.
