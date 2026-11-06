(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RangeC HalfC VprintfC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module FwritePostC.
Definition LOWIMG_LO : Z := 0x10040.
Definition LOWIMG_HI : Z := 0x22c60.
Definition FRAME : int := 2128%uint63.

Section WithSegs.
Variable segs : list Segment.

Definition cell_addr (fp : sv) (i : int) : sv := sv_alu ALU_ADD fp (VL (wsub (wlit (PrimInt63.mul 8%uint63 i)) (wlit 56%uint63))).
Definition load8 (st : sstate) (a : sv) : option sv :=
  match do_load segs st a 8%uint63 false with inl (Some v) => Some v | _ => None end.

Definition fwp_regs (fp : sv) (rav : w64) (v5 v4 v3 v2 v1 v0 : sv) : list (r5 * sv) :=
  [(X1, VL rav); (X2, fp); (X8, v0); (X9, v1); (X18, v2); (X19, v3); (X20, v4); (X21, v5)].

Definition afwrite_post_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl0, st1) =>
      match getr st X2, getr st X8, getr st X9, getr st X10, getr st X18 with
      | VP ks o2, VP k8 o8, VL size, VL res, VL p =>
          match IMap.find ks (s_regs st) with
          | Some rss =>
              let N := to_Z (wl res) * to_Z (wl size) in
              if PrimInt63.eqb ks k8 && weqb (wadd o2 (wlit FRAME)) o8 && RangeC.in_region rss o2 FRAME
                 && negb (wt size) && negb (wt res) && negb (wt p) && Z.leb 1 (to_Z (wl size)) && Z.leb N 4096
                 && Z.leb LOWIMG_LO (to_Z (wl p)) && Z.leb (to_Z (wl p) + N + 64) LOWIMG_HI
                 && CtrS.is_lit (getr st X21) (wlit 1%uint63)
                 && match find_op VprintfC.ZRO_ID (s_ops st) with Some [] => true | _ => false end
              then
                let st2 := setpc (setr (clobber st1) X10 (VL res)) r in
                let fp := VP ks o8 in
                match load8 st2 (cell_addr fp 0%uint63), load8 st2 (cell_addr fp 1%uint63), load8 st2 (cell_addr fp 2%uint63),
                      load8 st2 (cell_addr fp 3%uint63), load8 st2 (cell_addr fp 4%uint63), load8 st2 (cell_addr fp 5%uint63),
                      load8 st2 (cell_addr fp 6%uint63) with
                | Some v5, Some v4, Some v3, Some v2, Some v1, Some v0, Some (VL rav) =>
                    if negb (wt rav) && PrimInt63.ltb (wl rav) 4611686018427387904%uint63 && PrimInt63.eqb (PrimInt63.land (wl rav) 1%uint63) 0%uint63
                    then Some [setpc (HalfC.set_regs st2 (fwp_regs fp rav v5 v4 v3 v2 v1 v0)) (wl rav)]
                    else None
                | _, _, _, _, _, _, _ => None
                end
              else None
          | None => None
          end
      | _, _, _, _, _ => None
      end
  | None => None
  end.

Definition afwrite_post_c (pc : int) : contract := Contract pc afwrite_post_apply.
End WithSegs.
End FwritePostC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Actr.TwinB.
Import RangeC.TwinB HalfC.TwinB VprintfC.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module FwritePostC.
Definition LOWIMG_LO : Z := 0x10040.
Definition LOWIMG_HI : Z := 0x22d00.
Definition FRAME : int := 2128%uint63.

Section WithSegs.
Variable segs : list Segment.

Definition cell_addr (fp : sv) (i : int) : sv := sv_alu ALU_ADD fp (VL (wsub (wlit (PrimInt63.mul 8%uint63 i)) (wlit 56%uint63))).
Definition load8 (st : sstate) (a : sv) : option sv :=
  match do_load segs st a 8%uint63 false with inl (Some v) => Some v | _ => None end.

Definition fwp_regs (fp : sv) (rav : w64) (v5 v4 v3 v2 v1 v0 : sv) : list (r5 * sv) :=
  [(X1, VL rav); (X2, fp); (X8, v0); (X9, v1); (X18, v2); (X19, v3); (X20, v4); (X21, v5)].

Definition afwrite_post_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl0, st1) =>
      match getr st X2, getr st X8, getr st X9, getr st X10, getr st X18 with
      | VP ks o2, VP k8 o8, VL size, VL res, VL p =>
          match IMap.find ks (s_regs st) with
          | Some rss =>
              let N := to_Z (wl res) * to_Z (wl size) in
              if PrimInt63.eqb ks k8 && weqb (wadd o2 (wlit FRAME)) o8 && RangeC.TwinB.RangeC.in_region rss o2 FRAME
                 && negb (wt size) && negb (wt res) && negb (wt p) && Z.leb 1 (to_Z (wl size)) && Z.leb N 4096
                 && Z.leb LOWIMG_LO (to_Z (wl p)) && Z.leb (to_Z (wl p) + N + 64) LOWIMG_HI
                 && CtrS.is_lit (getr st X21) (wlit 1%uint63)
                 && match find_op VprintfC.TwinB.VprintfC.ZRO_ID (s_ops st) with Some [] => true | _ => false end
              then
                let st2 := setpc (setr (clobber st1) X10 (VL res)) r in
                let fp := VP ks o8 in
                match load8 st2 (cell_addr fp 0%uint63), load8 st2 (cell_addr fp 1%uint63), load8 st2 (cell_addr fp 2%uint63),
                      load8 st2 (cell_addr fp 3%uint63), load8 st2 (cell_addr fp 4%uint63), load8 st2 (cell_addr fp 5%uint63),
                      load8 st2 (cell_addr fp 6%uint63) with
                | Some v5, Some v4, Some v3, Some v2, Some v1, Some v0, Some (VL rav) =>
                    if negb (wt rav) && PrimInt63.ltb (wl rav) 4611686018427387904%uint63 && PrimInt63.eqb (PrimInt63.land (wl rav) 1%uint63) 0%uint63
                    then Some [setpc (HalfC.TwinB.HalfC.set_regs st2 (fwp_regs fp rav v5 v4 v3 v2 v1 v0)) (wl rav)]
                    else None
                | _, _, _, _, _, _, _ => None
                end
              else None
          | None => None
          end
      | _, _, _, _, _ => None
      end
  | None => None
  end.

Definition afwrite_post_c (pc : int) : contract := Contract pc afwrite_post_apply.
End WithSegs.
End FwritePostC.
End TwinB.
