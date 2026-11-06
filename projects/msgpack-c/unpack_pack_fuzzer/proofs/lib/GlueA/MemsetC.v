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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RangeC.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require KnownT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MemsetC.
Definition NMAX : int := 4096%uint63.

Definition in_region (r : region) (o : w64) (len : int) : bool :=
  match okey o, okey (wadd o (wlit len)), rg_hi r with
  | Some k0, Some k1, VL hi => kleb (rg_lo r) k0 && kleb k0 k1 && negb (wt hi) &&
                               (match okey hi with Some kh => kleb k1 kh | None => false end)
  | _, _, _ => false
  end.

Section WithSegs.
Variable segs : list Segment.
Definition rep8 (b : int) : w64 :=
  W64 (PrimInt63.leb 128%uint63 b) (PrimInt63.land (PrimInt63.mul b 0x0101010101010101%uint63) 9223372036854775807%uint63).
Fixpoint set_bytes (fuel : nat) (i : int) (dst : sv) (ofs : int) (b len : int) (st : sstate) : option sstate :=
  match fuel with
  | O => if PrimInt63.leb len i then Some st else None
  | S f =>
      if PrimInt63.leb len i then Some st else
      let w8 := PrimInt63.leb 8%uint63 (PrimInt63.sub len i) && PrimInt63.eqb (PrimInt63.land (PrimInt63.add ofs i) 7%uint63) 0%uint63 in
      let w := if w8 then 8%uint63 else 1%uint63 in
      let v := if w8 then VL (rep8 b) else VL (wlit b) in
      match do_store segs st (sv_alu ALU_ADD dst (VL (wlit i))) w v with
      | inl st' => set_bytes f (PrimInt63.add i w) dst ofs b len st'
      | inr _ => None
      end
  end.

Definition in_window (st : sstate) (wl : list (int * sv * w64)) (kd : int) (od : w64) (len : int) : bool :=
  match CtrA.win_lookup wl kd with
  | Some (wlen, kind) => negb (weqb kind ActrA.K_TWIN) && negb (PrimInt63.eqb kd 0%uint63) && negb (wt od) && negb (wt (wadd od (wlit len)))
                         && wleu od (wadd od (wlit len)) && KnownT.KnownT.known_leu_t (s_facts st) (VL (wadd od (wlit len))) wlen
  | None => false
  end.

Definition set_bytes_post (r kd : int) (od : w64) (b len : int) (st2 : sstate) : option (list sstate) :=
  match set_bytes (Z.to_nat (to_Z len) + 1) 0%uint63 (VP kd od) (W64.wl od) b len st2 with
  | Some stn => Some [stn]
  | None => None
  end.

Definition amemset_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10, getr st X11, getr st X12 with
      | VP kd od, VL c, VL n =>
          let len := W64.wl n in let b := PrimInt63.land (W64.wl c) 255%uint63 in
          if negb (wt n) && PrimInt63.leb 1%uint63 len && PrimInt63.leb len NMAX
             && match RangeC.range_class segs st wl kd od len true with Some _ => true | None => false end
          then set_bytes_post r kd od b len (setpc (setr (clobber st1) X10 (VP kd od)) r)
          else None
      | _, _, _ => None
      end
  | None => None
  end.

Definition amemset_c (pc : int) : contract := Contract pc amemset_apply.
End WithSegs.
End MemsetC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import RangeC.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module MemsetC.
Definition NMAX : int := 4096%uint63.

Definition in_region (r : region) (o : w64) (len : int) : bool :=
  match okey o, okey (wadd o (wlit len)), rg_hi r with
  | Some k0, Some k1, VL hi => kleb (rg_lo r) k0 && kleb k0 k1 && negb (wt hi) &&
                               (match okey hi with Some kh => kleb k1 kh | None => false end)
  | _, _, _ => false
  end.

Section WithSegs.
Variable segs : list Segment.
Definition rep8 (b : int) : w64 :=
  W64 (PrimInt63.leb 128%uint63 b) (PrimInt63.land (PrimInt63.mul b 0x0101010101010101%uint63) 9223372036854775807%uint63).
Fixpoint set_bytes (fuel : nat) (i : int) (dst : sv) (ofs : int) (b len : int) (st : sstate) : option sstate :=
  match fuel with
  | O => if PrimInt63.leb len i then Some st else None
  | S f =>
      if PrimInt63.leb len i then Some st else
      let w8 := PrimInt63.leb 8%uint63 (PrimInt63.sub len i) && PrimInt63.eqb (PrimInt63.land (PrimInt63.add ofs i) 7%uint63) 0%uint63 in
      let w := if w8 then 8%uint63 else 1%uint63 in
      let v := if w8 then VL (rep8 b) else VL (wlit b) in
      match do_store segs st (sv_alu ALU_ADD dst (VL (wlit i))) w v with
      | inl st' => set_bytes f (PrimInt63.add i w) dst ofs b len st'
      | inr _ => None
      end
  end.

Definition in_window (st : sstate) (wl : list (int * sv * w64)) (kd : int) (od : w64) (len : int) : bool :=
  match CtrA.win_lookup wl kd with
  | Some (wlen, kind) => negb (weqb kind ActrA.K_TWIN) && negb (PrimInt63.eqb kd 0%uint63) && negb (wt od) && negb (wt (wadd od (wlit len)))
                         && wleu od (wadd od (wlit len)) && KnownT.KnownT.known_leu_t (s_facts st) (VL (wadd od (wlit len))) wlen
  | None => false
  end.

Definition set_bytes_post (r kd : int) (od : w64) (b len : int) (st2 : sstate) : option (list sstate) :=
  match set_bytes (Z.to_nat (to_Z len) + 1) 0%uint63 (VP kd od) (W64.wl od) b len st2 with
  | Some stn => Some [stn]
  | None => None
  end.

Definition amemset_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match getr st X10, getr st X11, getr st X12 with
      | VP kd od, VL c, VL n =>
          let len := W64.wl n in let b := PrimInt63.land (W64.wl c) 255%uint63 in
          if negb (wt n) && PrimInt63.leb 1%uint63 len && PrimInt63.leb len NMAX
             && match RangeC.TwinB.RangeC.range_class segs st wl kd od len true with Some _ => true | None => false end
          then set_bytes_post r kd od b len (setpc (setr (clobber st1) X10 (VP kd od)) r)
          else None
      | _, _, _ => None
      end
  | None => None
  end.

Definition amemset_c (pc : int) : contract := Contract pc amemset_apply.
End WithSegs.
End MemsetC.
End TwinB.
