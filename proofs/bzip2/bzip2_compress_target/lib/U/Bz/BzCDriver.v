(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCSortF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCHuff BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams BzParamsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {BZP : BzParams}.


Definition BZ_RUN : Z := 0. Definition BZ_FLUSH : Z := 1. Definition BZ_FINISH : Z := 2.
Definition BZ_OK : Z := 0. Definition BZ_RUN_OK : Z := 1. Definition BZ_FLUSH_OK : Z := 2.
Definition BZ_FINISH_OK : Z := 3. Definition BZ_STREAM_END : Z := 4.
Definition BZ_SEQUENCE_ERROR : Z := -1. Definition BZ_PARAM_ERROR : Z := -2.
Definition BZ_MAX_UNUSED : Z := 5000.

(* [comment removed for export] *)
Record zstrm := ZS { z_in : list Z; z_avail_in : Z; z_outr : list Z; z_avail_out : Z;
                     z_tin_lo : Z; z_tin_hi : Z; z_tout_lo : Z; z_tout_hi : Z }.

Definition inc64 (lo hi : Z) : Z * Z :=
  let lo' := (lo + 1) mod 4294967296 in (lo', if lo' =? 0 then hi + 1 else hi).

(* [comment removed for export] *)
Definition ci_step (e : est) (z : zstrm) : est * zstrm :=
  match z_in z with
  | [] => (e, z)
  | c :: rest =>
      let e' := est_set_rl e (add_char_to_block (est_rl e) c) in
      let '(lo, hi) := inc64 (z_tin_lo z) (z_tin_hi z) in
      (e', ZS rest (z_avail_in z - 1) (z_outr z) (z_avail_out z) lo hi (z_tout_lo z) (z_tout_hi z))
  end.
(* [comment removed for export] *)
Fixpoint copy_input (fuel : nat) (e : est) (z : zstrm) (progress : bool) : est * zstrm * bool :=
  match fuel with
  | O => (e, z, progress)
  | S f =>
      if NBLOCKMAX <=? e_nblock e then (e, z, progress) else
      if z_avail_in z =? 0 then (e, z, progress) else
      if e_mode e =? BZ_M_RUNNING then
        let '(e, z) := ci_step e z in copy_input f e z true
      else
        if e_avail_in_expect e =? 0 then (e, z, progress) else
        let '(e, z) := ci_step e z in
        let e := est_set_modes e (e_mode e) (e_state e) (e_avail_in_expect e - 1) in
        copy_input f e z true
  end.

(* [comment removed for export] *)
Fixpoint copy_output (fuel : nat) (e : est) (z : zstrm) (progress : bool) : est * zstrm * bool :=
  match fuel with
  | O => (e, z, progress)
  | S f =>
      if z_avail_out z =? 0 then (e, z, progress) else
      if bw_numZ (e_bw e) <=? e_state_out_pos e then (e, z, progress) else
      let c := zget (bw_zb (e_bw e)) (e_state_out_pos e) in
      let '(lo, hi) := inc64 (z_tout_lo z) (z_tout_hi z) in
      copy_output f (est_set_outpos e (e_state_out_pos e + 1))
                  (ZS (z_in z) (z_avail_in z) (c :: z_outr z) (z_avail_out z - 1) (z_tin_lo z) (z_tin_hi z) lo hi) true
  end.

(* [comment removed for export] *)
Definition prepare_new_block (e : est) : est :=
  let r := prepare_new_block_rl (est_rl e) in
  let e := est_set_rl e r in
  EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
      (e_state_in_ch e) (e_state_in_len e) (e_nblock e) 0 (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
      (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew) (e_blockCRC e) (e_combinedCRC e) (e_blockNo e + 1)
      (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e) (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).

Definition isempty_RL_e (e : est) : bool := isempty_RL (est_rl e).

(* [comment removed for export] *)
Definition hc_iter (lj : zarr) (e : est) (z : zstrm) (pin pout : bool) : est * zstrm * bool * bool * bool :=
  (* [comment removed for export] *)
  let '(e, z, pout, brk) :=
    (if e_state e =? BZ_S_OUTPUT then
       let '(e, z, pout) := copy_output (Z.to_nat (z_avail_out z) + 1)%nat e z pout in
       if e_state_out_pos e <? bw_numZ (e_bw e) then (e, z, pout, true) else
       if (e_mode e =? BZ_M_FINISHING) && (e_avail_in_expect e =? 0) && isempty_RL_e e then (e, z, pout, true) else
       let e := prepare_new_block e in
       let e := est_set_modes e (e_mode e) BZ_S_INPUT (e_avail_in_expect e) in
       if (e_mode e =? BZ_M_FLUSHING) && (e_avail_in_expect e =? 0) && isempty_RL_e e then (e, z, pout, true)
       else (e, z, pout, false)
     else (e, z, pout, false)) in
  if brk then (e, z, pin, pout, true) else
  (* [comment removed for export] *)
  if e_state e =? BZ_S_INPUT then
    let '(e, z, pin) := copy_input (Z.to_nat (z_avail_in z) + 1)%nat e z pin in
    if negb (e_mode e =? BZ_M_RUNNING) && (e_avail_in_expect e =? 0) then
      let e := est_set_rl e (flush_RL (est_rl e)) in
      let '(e, _) := compressBlock e (e_mode e =? BZ_M_FINISHING) lj in
      (est_set_modes e (e_mode e) BZ_S_OUTPUT (e_avail_in_expect e), z, pin, pout, false)
    else if NBLOCKMAX <=? e_nblock e then
      let '(e, _) := compressBlock e false lj in
      (est_set_modes e (e_mode e) BZ_S_OUTPUT (e_avail_in_expect e), z, pin, pout, false)
    else if z_avail_in z =? 0 then (e, z, pin, pout, true)
    else (e, z, pin, pout, false)
  else (e, z, pin, pout, false).

Fixpoint hc_loop (fuel : nat) (lj : zarr) (e : est) (z : zstrm) (pin pout : bool) : est * zstrm * bool :=
  match fuel with
  | O => (e, z, pin || pout)
  | S f => let '(e, z, pin, pout, brk) := hc_iter lj e z pin pout in
           if brk then (e, z, pin || pout) else hc_loop f lj e z pin pout
  end.
(* [comment removed for export] *)
Definition hc_fuel (z : zstrm) : nat := Z.to_nat (2 * (z_avail_in z / NBLOCKMAX) + 2 * BZ_MAX_UNUSED + 8).
Definition handle_compress (lj : zarr) (e : est) (z : zstrm) : est * zstrm * bool :=
  hc_loop (hc_fuel z) lj e z false false.

(* [comment removed for export] *)
Definition bzCompress (lj : zarr) (e : est) (z : zstrm) (action : Z) : Z * est * zstrm :=
  let mode := e_mode e in
  (* [comment removed for export] *)
  let '(e, mode, err) :=
    (if mode =? BZ_M_RUNNING then
       if action =? BZ_RUN then (e, mode, false)
       else if action =? BZ_FLUSH then (est_set_modes e BZ_M_FLUSHING (e_state e) (z_avail_in z), BZ_M_FLUSHING, false)
       else if action =? BZ_FINISH then (est_set_modes e BZ_M_FINISHING (e_state e) (z_avail_in z), BZ_M_FINISHING, false)
       else (e, mode, true)
     else (e, mode, false)) in
  if err then (BZ_PARAM_ERROR, e, z) else
  if mode =? BZ_M_IDLE then (BZ_SEQUENCE_ERROR, e, z) else
  if mode =? BZ_M_RUNNING then
    let '(e, z, progress) := handle_compress lj e z in
    ((if progress then BZ_RUN_OK else BZ_PARAM_ERROR), e, z)
  else if mode =? BZ_M_FLUSHING then
    if negb (action =? BZ_FLUSH) then (BZ_SEQUENCE_ERROR, e, z) else
    if negb (e_avail_in_expect e =? z_avail_in z) then (BZ_SEQUENCE_ERROR, e, z) else
    let '(e, z, progress) := handle_compress lj e z in
    if (0 <? e_avail_in_expect e) || negb (isempty_RL_e e) || (e_state_out_pos e <? bw_numZ (e_bw e)) then (BZ_FLUSH_OK, e, z)
    else (BZ_RUN_OK, est_set_modes e BZ_M_RUNNING (e_state e) (e_avail_in_expect e), z)
  else (* [comment removed for export] *)
    if negb (action =? BZ_FINISH) then (BZ_SEQUENCE_ERROR, e, z) else
    if negb (e_avail_in_expect e =? z_avail_in z) then (BZ_SEQUENCE_ERROR, e, z) else
    let '(e, z, progress) := handle_compress lj e z in
    if negb progress then (BZ_SEQUENCE_ERROR, e, z) else
    if (0 <? e_avail_in_expect e) || negb (isempty_RL_e e) || (e_state_out_pos e <? bw_numZ (e_bw e)) then (BZ_FINISH_OK, e, z)
    else (BZ_STREAM_END, est_set_modes e BZ_M_IDLE (e_state e) (e_avail_in_expect e), z).

(* [comment removed for export] *)
Record wsession := WS { ws_chunks : list (list Z); ws_err_write : Z; ws_err_close : Z; ws_e : est; ws_z : zstrm }.

(* [comment removed for export] *)
Fixpoint bzWrite_loop (fuel : nat) (lj : zarr) (e : est) (z : zstrm) (acc : list (list Z)) : list (list Z) * Z * est * zstrm :=
  match fuel with
  | O => (acc, BZ_OK, e, z)
  | S f =>
      let z := ZS (z_in z) (z_avail_in z) [] BZ_MAX_UNUSED (z_tin_lo z) (z_tin_hi z) (z_tout_lo z) (z_tout_hi z) in
      let '(ret, e, z) := bzCompress lj e z BZ_RUN in
      if negb (ret =? BZ_RUN_OK) then (acc, ret, e, z) else
      let acc := if z_avail_out z <? BZ_MAX_UNUSED then acc ++ [rev (z_outr z)] else acc in
      if z_avail_in z =? 0 then (acc, BZ_OK, e, z) else bzWrite_loop f lj e z acc
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition write_phase (lj : zarr) (e0 : est) (payload : list Z) : list (list Z) * Z * est * zstrm :=
  let len := Z.of_nat (length payload) in
  let fuel := Z.to_nat (len / 1000 + 16) in
  let z0 := ZS payload len [] 0 0 0 0 0 in
  if len =? 0 then ([], BZ_OK, e0, z0) else bzWrite_loop fuel lj e0 z0 [].
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition est0 : est := est_init znew znew znew znew znew znew znew znew znew znew znew znew 0 0 0 0 0.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

End ACeilS1.
