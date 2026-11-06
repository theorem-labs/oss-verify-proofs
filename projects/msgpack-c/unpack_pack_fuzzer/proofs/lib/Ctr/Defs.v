(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module CtrS.

Definition FD3_ID : int := 2%uint63.
Definition RSTAGE_ID : int := 3%uint63.
Definition FD3DIR_ID : int := 4%uint63.
Definition FDINIT_ID : int := 5%uint63.

Definition SIZE10 : sv := VBlob false 10%uint63 (VL wzero) 8%uint63.
Definition SIZE11 : sv := VBlob false 11%uint63 (VL wzero) 8%uint63.

Definition is_lit (v : sv) (w : w64) : bool := sv_eqb v (VL w).
Definition neg (e : Z) : w64 := Z2w (- e).
Definition errv (e : Z) : sv := VL (neg e).

Definition pc_ok (st : sstate) : bool := PrimInt63.ltb (s_pc st) bit62i.

Definition is_fd_op (o : opinst) : bool :=
  PrimInt63.eqb (op_id o) FDINIT_ID || PrimInt63.eqb (op_id o) FD3_ID || PrimInt63.eqb (op_id o) FD3DIR_ID.
Fixpoint count_fd_ops (os : list opinst) : nat :=
  match os with [] => 0%nat | o :: os' => ((if is_fd_op o then 1 else 0) + count_fd_ops os')%nat end.
Definition one_fd_op (st : sstate) : bool := Nat.eqb (count_fd_ops (s_ops st)) 1%nat.

Definition sysno (st : sstate) (n : int) : bool := is_lit (getr st X17) (wlit n) && pc_ok st && one_fd_op st.

Definition priv_has (st : sstate) (lo len : int) : bool :=
  existsb (fun iv => PrimInt63.eqb (fst iv) lo && PrimInt63.eqb (snd iv) (PrimInt63.add lo len)) (s_priv st).

Section WithImg.

Variable READ_STAGE : int.
Definition STAGE_LEN : int := 65536%uint63.

Definition AT_FDCWD_w : w64 := neg 100.
Definition open_flags_ok (v : sv) : bool := is_lit v (wlit 32768%uint63) || is_lit v wzero.

Definition region10_ok (st : sstate) : bool :=
  match IMap.find 10%uint63 (s_regs st) with
  | Some (Region lo hi w (BGBlob j sh) cells) =>
      PrimInt63.eqb lo 0%uint63 && sv_eqb hi SIZE10 && negb w && PrimInt63.eqb j 3%uint63 && PrimInt63.eqb sh 0%uint63
      && match cells with IMap.Leaf => true | _ => false end
  | _ => false
  end.

Definition open_pre (st : sstate) : bool :=
  sysno st 56%uint63 && is_lit (getr st X10) AT_FDCWD_w && sv_eqb (getr st X11) (VP 10%uint63 wzero)
  && open_flags_ok (getr st X12) && region10_ok st
  && match find_op FDINIT_ID (s_ops st) with Some [] => true | _ => false end.

Definition open_errnos : list Z := [ENOMEM; EACCES; EMFILE; ENFILE].
Definition open_err_posts (st : sstate) : list sstate := map (fun e => sysret st (errv e)) open_errnos.

Definition open_file_apply (st : sstate) : option (list sstate) :=
  if open_pre st then
    Some (sysret (set_ops st (OpI FD3_ID [VL wzero] :: remove_op FDINIT_ID (s_ops st))) (VL (wlit 3%uint63))
          :: open_err_posts st)
  else None.

Definition open_dir_apply (st : sstate) : option (list sstate) :=
  if open_pre st then
    Some (sysret (set_ops st (OpI FD3DIR_ID [] :: remove_op FDINIT_ID (s_ops st))) (VL (wlit 3%uint63))
          :: open_err_posts st)
  else None.

Definition open_absent_apply (st : sstate) : option (list sstate) :=
  if open_pre st then Some [sysret st (errv ENOENT)] else None.

Definition open_toolong_apply (st : sstate) : option (list sstate) :=
  if open_pre st then Some [sysret st (errv ENAMETOOLONG)] else None.

Fixpoint count_ops (id : int) (os : list opinst) : nat :=
  match os with [] => 0%nat | o :: os' => ((if PrimInt63.eqb (op_id o) id then 1 else 0) + count_ops id os')%nat end.

Definition read_pre (st : sstate) : option sv :=
  if sysno st 63%uint63 && is_lit (getr st X10) (wlit 3%uint63) && is_lit (getr st X11) (wlit READ_STAGE)
     && priv_has st READ_STAGE STAGE_LEN
     && match find_op RSTAGE_ID (s_ops st) with Some [_; _] => Nat.eqb (count_ops RSTAGE_ID (s_ops st)) 1%nat | _ => false end
  then match find_op FD3_ID (s_ops st) with Some [off] => Some off | _ => None end
  else None.

Definition want_ok (v : sv) : option w64 :=
  match v with
  | VL w => if wltu wzero w && wleu w (wlit STAGE_LEN) then Some w else None
  | _ => None
  end.

Definition OFF_MAX : sv := VL (wlit 1099511627776%uint63).

Definition read_file_apply (st : sstate) : option (list sstate) :=
  match read_pre st with
  | Some off =>
      let fs := s_facts st in
      if known_leu fs SIZE11 off then
        (if known_leu fs off OFF_MAX && known_leu fs (getr st X12) OFF_MAX
         then Some [sysret (set_ops st (set_op RSTAGE_ID [off; VL wzero] (s_ops st))) (VL wzero)]
         else None)
      else
        match want_ok (getr st X12) with
        | Some w =>
            let e := sv_alu ALU_ADD off (VL w) in
            if negb (known_leu fs e OFF_MAX) then None else
            let stA := addfact (sysret (set_ops st (set_op FD3_ID [e] (set_op RSTAGE_ID [off; VL w] (s_ops st)))) (VL w))
                               (FULe e SIZE11) in
            let nB := sv_alu ALU_SUB SIZE11 off in
            let stB := addfact (sysret (set_ops st (set_op FD3_ID [SIZE11] (set_op RSTAGE_ID [off; nB] (s_ops st)))) nB)
                               (FULt SIZE11 e) in
            match decide_ltu fs SIZE11 e with
            | Some false => Some [stA]
            | Some true => Some [stB]
            | None => Some [stA; stB]
            end
        | None => None
        end
  | None => None
  end.

Definition read_dir_apply (st : sstate) : option (list sstate) :=
  if sysno st 63%uint63 && is_lit (getr st X10) (wlit 3%uint63) && is_lit (getr st X11) (wlit READ_STAGE)
     && match want_ok (getr st X12) with Some _ => true | None => is_lit (getr st X12) wzero end
     && match find_op FD3DIR_ID (s_ops st) with Some [] => true | _ => false end
  then Some [sysret st (errv EISDIR)] else None.

Definition close_apply (st : sstate) : option (list sstate) :=
  if sysno st 57%uint63 && is_lit (getr st X10) (wlit 3%uint63) then
    match find_op FD3_ID (s_ops st), find_op FD3DIR_ID (s_ops st) with
    | Some [_], None => Some [sysret (set_ops st (OpI FDINIT_ID [] :: remove_op FD3_ID (s_ops st))) (VL wzero)]
    | None, Some [] => Some [sysret (set_ops st (OpI FDINIT_ID [] :: remove_op FD3DIR_ID (s_ops st))) (VL wzero)]
    | _, _ => None
    end
  else None.

Definition has_fds (st : sstate) : bool :=
  match find_op FDINIT_ID (s_ops st), find_op FD3_ID (s_ops st), find_op FD3DIR_ID (s_ops st) with
  | Some [], _, _ | _, Some [_], _ | _, _, Some [] => true
  | _, _, _ => false
  end.

Definition ioctl_apply (st : sstate) : option (list sstate) :=
  if sysno st 29%uint63 && is_lit (getr st X10) (wlit 1%uint63) && is_lit (getr st X11) (wlit 21523%uint63) && has_fds st
  then Some [sysret st (errv ENOTTY)] else None.

Definition c_open_file (pc : int) : contract := Contract pc open_file_apply.
Definition c_open_dir (pc : int) : contract := Contract pc open_dir_apply.
Definition c_open_absent (pc : int) : contract := Contract pc open_absent_apply.
Definition c_open_toolong (pc : int) : contract := Contract pc open_toolong_apply.
Definition c_read_file (pc : int) : contract := Contract pc read_file_apply.
Definition c_read_dir (pc : int) : contract := Contract pc read_dir_apply.
Definition c_close (pc : int) : contract := Contract pc close_apply.
Definition c_ioctl (pc : int) : contract := Contract pc ioctl_apply.

End WithImg.
End CtrS.
