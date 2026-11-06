(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ReadC.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ReadDirC.
Import ReadC.

Section WithCfg.
Variable C : rcfg.

Definition aread_dir_pre (st : sstate) : bool :=
  CtrS.is_lit (getr st X10) (wlit 3%uint63) && CtrS.is_lit (getr st X11) (wlit (r_stage C))
  && CtrS.priv_has st (r_stage C) CtrS.STAGE_LEN
  && match CtrS.want_ok (getr st X12) with Some _ => true | None => false end
  && CtrS.one_fd_op st
  && match find_op CtrS.FD3DIR_ID (s_ops st) with Some [] => true | _ => false end
  && match find_op (r_zsh C) (s_ops st) with Some [] => true | _ => false end.

Definition MINUS1 : sv := CtrS.errv 1.

Definition aread_dir_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, _, _, st1) =>
      if aread_dir_pre st then
        match ActrA.errno_havoc (setr (clobber st1) X10 MINUS1) with
        | Some stE => Some [setpc stE r]
        | None => None
        end
      else None
  | None => None
  end.

Definition aread_dir_c (pc : int) : contract := Contract pc aread_dir_apply.
End WithCfg.

End ReadDirC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs.
Import Actr.TwinB.
Import ReadC.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ReadDirC.
Import ReadC.TwinB.ReadC.

Section WithCfg.
Variable C : rcfg.

Definition aread_dir_pre (st : sstate) : bool :=
  CtrS.is_lit (getr st X10) (wlit 3%uint63) && CtrS.is_lit (getr st X11) (wlit (r_stage C))
  && CtrS.priv_has st (r_stage C) CtrS.STAGE_LEN
  && match CtrS.want_ok (getr st X12) with Some _ => true | None => false end
  && CtrS.one_fd_op st
  && match find_op CtrS.FD3DIR_ID (s_ops st) with Some [] => true | _ => false end
  && match find_op (r_zsh C) (s_ops st) with Some [] => true | _ => false end.

Definition MINUS1 : sv := CtrS.errv 1.

Definition aread_dir_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, _, _, st1) =>
      if aread_dir_pre st then
        match ActrA.errno_havoc (setr (clobber st1) X10 MINUS1) with
        | Some stE => Some [setpc stE r]
        | None => None
        end
      else None
  | None => None
  end.

Definition aread_dir_c (pc : int) : contract := Contract pc aread_dir_apply.
End WithCfg.

End ReadDirC.
End TwinB.
