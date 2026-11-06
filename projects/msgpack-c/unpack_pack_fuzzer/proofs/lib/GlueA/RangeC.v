(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RangeC.
Definition NMAX : int := 4096%uint63.
Definition SBw : w64 := wlit 2147450880%uint63.
Definition SSH_ID : int := 12%uint63.
Definition ZRO_ID : int := 13%uint63.

Definition lit_low (st : sstate) (a : w64) (len : int) : bool :=
  negb (wt a) && PrimInt63.leb 65600%uint63 (W64.wl a) && PrimInt63.leb (W64.wl a) 142432%uint63
  && PrimInt63.leb (PrimInt63.add (W64.wl a) (PrimInt63.add len 64%uint63)) 142432%uint63
  && match find_op ZRO_ID (s_ops st) with Some [] => true | _ => false end.

Definition in_region (r : region) (o : w64) (len : int) : bool :=
  match okey o, okey (wadd o (wlit len)), rg_hi r with
  | Some k0, Some k1, VL hi => kleb (rg_lo r) k0 && kleb k0 k1 && negb (wt hi) &&
                               (match okey hi with Some kh => kleb k1 kh | None => false end)
  | _, _, _ => false
  end.

Section WithSegs.
Variable segs : list Segment.

Definition K_FRAME : w64 := wlit 7%uint63.
Definition K_FTWIN : w64 := wlit 8%uint63.

Definition K_SLOT : w64 := wlit 4%uint63.
Definition K_ZONE : w64 := wlit 5%uint63.
Definition pat_ok (st : sstate) (wl : list (int * sv * w64)) (k : int) (kind : w64) : bool :=
  if weqb kind CtrLib.K_BLOCK then ActrA.twin_pat_ok st wl k else (weqb kind K_SLOT || weqb kind K_ZONE).
Definition in_window (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) (len : int) : bool :=
  match CtrA.win_lookup wl k with
  | Some (wlen, kind) => if pat_ok st wl k kind then
                         negb (weqb kind K_FRAME) && negb (weqb kind K_FTWIN)
                         && negb (weqb kind ActrA.K_TWIN) && negb (PrimInt63.eqb k 0%uint63) && negb (wt o) && negb (wt (wadd o (wlit len)))
                         && wleu o (wadd o (wlit len)) && KnownT.KnownT.known_leu_t (s_facts st) (VL (wadd o (wlit len))) wlen
                         else false
  | None => false
  end.

Definition stack_side (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) : bool :=
  match ActrA.sp_region st with
  | Some (ks, offs, _) =>
      if PrimInt63.eqb k ks then Z.leb (w2Zs offs) (w2Zs o)
      else match CtrA.win_lookup wl k with None => true | Some _ => false end
  | None => false
  end.

Fixpoint zero_loads (fuel : nat) (st : sstate) (p : sv) : bool :=
  match fuel with
  | O => true
  | S f => match do_load segs st p 1%uint63 false with
           | inl (Some (VL z)) => weqb z wzero && zero_loads f st (sv_alu ALU_ADD p (VL (wlit 1%uint63)))
           | _ => false
           end
  end.

Definition shadow_zero_need (st : sstate) (k : int) (o : w64) (len : int) : nat :=
  if aligned (s_facts st) (VP k o) 3%uint63 then Z.to_nat ((to_Z len + 7) / 8) else (Z.to_nat ((to_Z len + 6) / 8) + 1)%nat.
Definition shadow_zero (st : sstate) (k : int) (o : w64) (len : int) : bool :=
  match shadow_fold (s_facts st) (VAlu ALU_SRL (VP k o) (VL (wlit 3%uint63))) (VL SBw) with
  | Some p => zero_loads (shadow_zero_need st k o len) st p
  | None => false
  end.

Definition K_CTOP : w64 := wlit 2%uint63.
Definition K_VTOP : w64 := wlit 3%uint63.
Definition K_ETOP : w64 := wlit 6%uint63.
Definition top_kind (kind : w64) : bool := weqb kind K_CTOP || weqb kind K_VTOP || weqb kind K_ETOP.
Definition in_view (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) (len : int) : bool :=
  match CtrA.win_lookup wl k with
  | Some (wlen, kind) => top_kind kind
                         && negb (PrimInt63.eqb k 0%uint63) && negb (wt o) && negb (wt (wadd o (wlit len)))
                         && wleu o (wadd o (wlit len)) && KnownT.KnownT.known_leu_t (s_facts st) (VL (wadd o (wlit len))) wlen
                         && shadow_zero st k o len
  | None => false
  end.

Fixpoint gran_loads (fuel : nat) (need_last : int) (st : sstate) (p : sv) : bool :=
  match fuel with
  | O => true
  | S f => match do_load segs st p 1%uint63 false with
           | inl (Some (VL z)) =>
               (weqb z wzero || match f with
                                | O => negb (wt z) && PrimInt63.leb need_last (W64.wl z) && PrimInt63.leb (W64.wl z) 7%uint63
                                | S _ => false
                                end)
               && gran_loads f need_last st (sv_alu ALU_ADD p (VL (wlit 1%uint63)))
           | _ => false
           end
  end.
Definition shadow_ok_x (st : sstate) (k : int) (o : w64) (len : int) : bool :=
  let tot := PrimInt63.add (PrimInt63.land (W64.wl o) 7%uint63) len in
  let need := PrimInt63.add (PrimInt63.land (PrimInt63.sub tot 1%uint63) 7%uint63) 1%uint63 in
  aligned (s_facts st) (VP k wzero) 3%uint63 && negb (wt o) &&
  match shadow_fold (s_facts st) (VAlu ALU_SRL (VP k o) (VL (wlit 3%uint63))) (VL SBw) with
  | Some p => gran_loads (Z.to_nat ((to_Z tot + 7) / 8)) need st p
  | None => false
  end.
Definition in_frame (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) (len : int) : bool :=
  match CtrA.win_lookup wl k with
  | Some (wlen, kind) => weqb kind K_FRAME && negb (PrimInt63.eqb k 0%uint63) && negb (wt o) && negb (wt (wadd o (wlit len)))
                         && wleu o (wadd o (wlit len)) && KnownT.KnownT.known_leu_t (s_facts st) (VL (wadd o (wlit len))) wlen
                         && aligned (s_facts st) (VP k wzero) 6%uint63
  | None => false
  end.

Definition not_view (fs : list fact) (k : int) (r : region) : bool :=
  match ActrA.zero_view r with Some _ => false | None => true end && match ActrA.find_pin fs k with Some _ => false | None => true end.

Inductive rclass := RC_WIN | RC_STK | RC_FRM | RC_VIEW.
Definition range_class (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) (len : int) (needw : bool) : option rclass :=
  match IMap.find k (s_regs st) with
  | Some r =>
      if negb (PrimInt63.eqb k 0%uint63) && implb needw (rg_w r) then
        if in_window st wl k o len then Some RC_WIN
        else if in_view st wl k o len then Some RC_VIEW
        else if in_frame st wl k o len && shadow_ok_x st k o len then Some RC_FRM
        else if not_view (s_facts st) k r && in_region r o (PrimInt63.add len 8%uint63) && stack_side st wl k o && shadow_zero st k o len
                && match find_op SSH_ID (s_ops st) with Some [] => true | _ => false end then Some RC_STK
        else None
      else None
  | None => None
  end.
End WithSegs.
End RangeC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RangeC.
Definition NMAX : int := 4096%uint63.
Definition SBw : w64 := wlit 2147450880%uint63.
Definition SSH_ID : int := 12%uint63.
Definition ZRO_ID : int := 13%uint63.

Definition lit_low (st : sstate) (a : w64) (len : int) : bool :=
  negb (wt a) && PrimInt63.leb 65600%uint63 (W64.wl a) && PrimInt63.leb (W64.wl a) 142592%uint63
  && PrimInt63.leb (PrimInt63.add (W64.wl a) (PrimInt63.add len 64%uint63)) 142592%uint63
  && match find_op ZRO_ID (s_ops st) with Some [] => true | _ => false end.

Definition in_region (r : region) (o : w64) (len : int) : bool :=
  match okey o, okey (wadd o (wlit len)), rg_hi r with
  | Some k0, Some k1, VL hi => kleb (rg_lo r) k0 && kleb k0 k1 && negb (wt hi) &&
                               (match okey hi with Some kh => kleb k1 kh | None => false end)
  | _, _, _ => false
  end.

Section WithSegs.
Variable segs : list Segment.

Definition K_FRAME : w64 := wlit 7%uint63.
Definition K_FTWIN : w64 := wlit 8%uint63.

Definition K_SLOT : w64 := wlit 4%uint63.
Definition K_ZONE : w64 := wlit 5%uint63.
Definition pat_ok (st : sstate) (wl : list (int * sv * w64)) (k : int) (kind : w64) : bool :=
  if weqb kind CtrLib.K_BLOCK then ActrA.twin_pat_ok st wl k else (weqb kind K_SLOT || weqb kind K_ZONE).
Definition in_window (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) (len : int) : bool :=
  match CtrA.win_lookup wl k with
  | Some (wlen, kind) => if pat_ok st wl k kind then
                         negb (weqb kind K_FRAME) && negb (weqb kind K_FTWIN)
                         && negb (weqb kind ActrA.K_TWIN) && negb (PrimInt63.eqb k 0%uint63) && negb (wt o) && negb (wt (wadd o (wlit len)))
                         && wleu o (wadd o (wlit len)) && KnownT.KnownT.known_leu_t (s_facts st) (VL (wadd o (wlit len))) wlen
                         else false
  | None => false
  end.

Definition stack_side (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) : bool :=
  match ActrA.sp_region st with
  | Some (ks, offs, _) =>
      if PrimInt63.eqb k ks then Z.leb (w2Zs offs) (w2Zs o)
      else match CtrA.win_lookup wl k with None => true | Some _ => false end
  | None => false
  end.

Fixpoint zero_loads (fuel : nat) (st : sstate) (p : sv) : bool :=
  match fuel with
  | O => true
  | S f => match do_load segs st p 1%uint63 false with
           | inl (Some (VL z)) => weqb z wzero && zero_loads f st (sv_alu ALU_ADD p (VL (wlit 1%uint63)))
           | _ => false
           end
  end.

Definition shadow_zero_need (st : sstate) (k : int) (o : w64) (len : int) : nat :=
  if aligned (s_facts st) (VP k o) 3%uint63 then Z.to_nat ((to_Z len + 7) / 8) else (Z.to_nat ((to_Z len + 6) / 8) + 1)%nat.
Definition shadow_zero (st : sstate) (k : int) (o : w64) (len : int) : bool :=
  match shadow_fold (s_facts st) (VAlu ALU_SRL (VP k o) (VL (wlit 3%uint63))) (VL SBw) with
  | Some p => zero_loads (shadow_zero_need st k o len) st p
  | None => false
  end.

Definition K_CTOP : w64 := wlit 2%uint63.
Definition K_VTOP : w64 := wlit 3%uint63.
Definition K_ETOP : w64 := wlit 6%uint63.
Definition top_kind (kind : w64) : bool := weqb kind K_CTOP || weqb kind K_VTOP || weqb kind K_ETOP.
Definition in_view (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) (len : int) : bool :=
  match CtrA.win_lookup wl k with
  | Some (wlen, kind) => top_kind kind
                         && negb (PrimInt63.eqb k 0%uint63) && negb (wt o) && negb (wt (wadd o (wlit len)))
                         && wleu o (wadd o (wlit len)) && KnownT.KnownT.known_leu_t (s_facts st) (VL (wadd o (wlit len))) wlen
                         && shadow_zero st k o len
  | None => false
  end.

Fixpoint gran_loads (fuel : nat) (need_last : int) (st : sstate) (p : sv) : bool :=
  match fuel with
  | O => true
  | S f => match do_load segs st p 1%uint63 false with
           | inl (Some (VL z)) =>
               (weqb z wzero || match f with
                                | O => negb (wt z) && PrimInt63.leb need_last (W64.wl z) && PrimInt63.leb (W64.wl z) 7%uint63
                                | S _ => false
                                end)
               && gran_loads f need_last st (sv_alu ALU_ADD p (VL (wlit 1%uint63)))
           | _ => false
           end
  end.
Definition shadow_ok_x (st : sstate) (k : int) (o : w64) (len : int) : bool :=
  let tot := PrimInt63.add (PrimInt63.land (W64.wl o) 7%uint63) len in
  let need := PrimInt63.add (PrimInt63.land (PrimInt63.sub tot 1%uint63) 7%uint63) 1%uint63 in
  aligned (s_facts st) (VP k wzero) 3%uint63 && negb (wt o) &&
  match shadow_fold (s_facts st) (VAlu ALU_SRL (VP k o) (VL (wlit 3%uint63))) (VL SBw) with
  | Some p => gran_loads (Z.to_nat ((to_Z tot + 7) / 8)) need st p
  | None => false
  end.
Definition in_frame (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) (len : int) : bool :=
  match CtrA.win_lookup wl k with
  | Some (wlen, kind) => weqb kind K_FRAME && negb (PrimInt63.eqb k 0%uint63) && negb (wt o) && negb (wt (wadd o (wlit len)))
                         && wleu o (wadd o (wlit len)) && KnownT.KnownT.known_leu_t (s_facts st) (VL (wadd o (wlit len))) wlen
                         && aligned (s_facts st) (VP k wzero) 6%uint63
  | None => false
  end.

Definition not_view (fs : list fact) (k : int) (r : region) : bool :=
  match ActrA.zero_view r with Some _ => false | None => true end && match ActrA.find_pin fs k with Some _ => false | None => true end.

Inductive rclass := RC_WIN | RC_STK | RC_FRM | RC_VIEW.
Definition range_class (st : sstate) (wl : list (int * sv * w64)) (k : int) (o : w64) (len : int) (needw : bool) : option rclass :=
  match IMap.find k (s_regs st) with
  | Some r =>
      if negb (PrimInt63.eqb k 0%uint63) && implb needw (rg_w r) then
        if in_window st wl k o len then Some RC_WIN
        else if in_view st wl k o len then Some RC_VIEW
        else if in_frame st wl k o len && shadow_ok_x st k o len then Some RC_FRM
        else if not_view (s_facts st) k r && in_region r o (PrimInt63.add len 8%uint63) && stack_side st wl k o && shadow_zero st k o len
                && match find_op SSH_ID (s_ops st) with Some [] => true | _ => false end then Some RC_STK
        else None
      else None
  | None => None
  end.
End WithSegs.
End RangeC.
End TwinB.
