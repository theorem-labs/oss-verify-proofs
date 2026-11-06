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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module ReadC.

Definition RSTV_ID : int := 15%uint63.

Record rcfg := RCfg {
  r_stage : int;
  r_zsh : int
}.

Section WithCfg.
Variable C : rcfg.

Definition aread_pre (st : sstate) : option sv :=
  if CtrS.is_lit (getr st X10) (wlit 3%uint63) && CtrS.is_lit (getr st X11) (wlit (r_stage C))
     && CtrS.priv_has st (r_stage C) CtrS.STAGE_LEN
     && match find_op RSTV_ID (s_ops st) with Some [_; _] => Nat.eqb (CtrS.count_ops RSTV_ID (s_ops st)) 1%nat | _ => false end
     && CtrS.one_fd_op st
     && match find_op (r_zsh C) (s_ops st) with Some [] => true | _ => false end
  then match find_op CtrS.FD3_ID (s_ops st) with Some [off] => Some off | _ => None end
  else None.

Definition ret_state (st1 : sstate) (r : int) (os' : list opinst) (v : sv) : sstate :=
  setpc (setr (set_ops (clobber st1) os') X10 v) r.

Definition pos_count (fs : list fact) (c : sv) : bool :=
  known_ltu fs (VL wzero) c || match c with VAlu ALU_SUB a b => known_ltu fs b a | _ => false end.

Definition aread_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match aread_pre st with
      | Some off =>
          let fs := s_facts st in let os := s_ops st in
          match CtrS.want_ok (getr st X12) with
          | Some w =>
              if known_leu fs CtrS.SIZE11 off then
                (if known_leu fs off CtrS.OFF_MAX
                 then Some [ret_state st1 r (set_op RSTV_ID [off; VL wzero] os) (VL wzero)]
                 else None)
              else
                let e := sv_alu ALU_ADD off (VL w) in
                if negb (known_leu fs e CtrS.OFF_MAX) then None else
                let stA := addfact (ret_state st1 r (set_op CtrS.FD3_ID [e] (set_op RSTV_ID [off; VL w] os)) (VL w)) (FULe e CtrS.SIZE11) in
                let nB := sv_alu ALU_SUB CtrS.SIZE11 off in
                let stB := addfact (ret_state st1 r (set_op CtrS.FD3_ID [CtrS.SIZE11] (set_op RSTV_ID [off; nB] os)) nB) (FULt CtrS.SIZE11 e) in
                match decide_ltu fs CtrS.SIZE11 e with
                | Some false => Some [stA]
                | Some true => Some [stB]
                | None => Some [stA; stB]
                end
          | None =>

              let c := getr st X12 in
              if pos_count fs c && known_leu fs c (VL (wlit CtrS.STAGE_LEN))
                 && known_leu fs CtrS.SIZE11 off && known_leu fs off CtrS.OFF_MAX
              then Some [ret_state st1 r (set_op RSTV_ID [off; VL wzero] os) (VL wzero)]
              else None
          end
      | None => None
      end
  | None => None
  end.

Definition aread_c (pc : int) : contract := Contract pc aread_apply.
End WithCfg.

Definition CFG_ASAN : rcfg := RCfg 6275344%uint63 11%uint63.

End ReadC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs.
Import Actr.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module ReadC.

Definition RSTV_ID : int := 15%uint63.

Record rcfg := RCfg {
  r_stage : int;
  r_zsh : int
}.

Section WithCfg.
Variable C : rcfg.

Definition aread_pre (st : sstate) : option sv :=
  if CtrS.is_lit (getr st X10) (wlit 3%uint63) && CtrS.is_lit (getr st X11) (wlit (r_stage C))
     && CtrS.priv_has st (r_stage C) CtrS.STAGE_LEN
     && match find_op RSTV_ID (s_ops st) with Some [_; _] => Nat.eqb (CtrS.count_ops RSTV_ID (s_ops st)) 1%nat | _ => false end
     && CtrS.one_fd_op st
     && match find_op (r_zsh C) (s_ops st) with Some [] => true | _ => false end
  then match find_op CtrS.FD3_ID (s_ops st) with Some [off] => Some off | _ => None end
  else None.

Definition ret_state (st1 : sstate) (r : int) (os' : list opinst) (v : sv) : sstate :=
  setpc (setr (set_ops (clobber st1) os') X10 v) r.

Definition pos_count (fs : list fact) (c : sv) : bool :=
  known_ltu fs (VL wzero) c || match c with VAlu ALU_SUB a b => known_ltu fs b a | _ => false end.

Definition aread_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      match aread_pre st with
      | Some off =>
          let fs := s_facts st in let os := s_ops st in
          match CtrS.want_ok (getr st X12) with
          | Some w =>
              if known_leu fs CtrS.SIZE11 off then
                (if known_leu fs off CtrS.OFF_MAX
                 then Some [ret_state st1 r (set_op RSTV_ID [off; VL wzero] os) (VL wzero)]
                 else None)
              else
                let e := sv_alu ALU_ADD off (VL w) in
                if negb (known_leu fs e CtrS.OFF_MAX) then None else
                let stA := addfact (ret_state st1 r (set_op CtrS.FD3_ID [e] (set_op RSTV_ID [off; VL w] os)) (VL w)) (FULe e CtrS.SIZE11) in
                let nB := sv_alu ALU_SUB CtrS.SIZE11 off in
                let stB := addfact (ret_state st1 r (set_op CtrS.FD3_ID [CtrS.SIZE11] (set_op RSTV_ID [off; nB] os)) nB) (FULt CtrS.SIZE11 e) in
                match decide_ltu fs CtrS.SIZE11 e with
                | Some false => Some [stA]
                | Some true => Some [stB]
                | None => Some [stA; stB]
                end
          | None =>

              let c := getr st X12 in
              if pos_count fs c && known_leu fs c (VL (wlit CtrS.STAGE_LEN))
                 && known_leu fs CtrS.SIZE11 off && known_leu fs off CtrS.OFF_MAX
              then Some [ret_state st1 r (set_op RSTV_ID [off; VL wzero] os) (VL wzero)]
              else None
          end
      | None => None
      end
  | None => None
  end.

Definition aread_c (pc : int) : contract := Contract pc aread_apply.
End WithCfg.

Definition CFG_ASAN : rcfg := RCfg 6283984%uint63 11%uint63.

End ReadC.
End TwinB.
