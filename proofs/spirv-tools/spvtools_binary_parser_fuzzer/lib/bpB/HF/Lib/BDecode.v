(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BLPropExec BMState BMem BITree BLNodes.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Fixpoint listNN_eqb (l1 l2 : list (word * word)) : bool :=
  match l1, l2 with
  | [], [] => true
  | (a1, n1) :: r1, (a2, n2) :: r2 =>
      bv_eqb a1 a2 && bv_eqb n1 n2 && listNN_eqb r1 r2
  | _, _ => false
  end.

Definition errno_of (r : word) : option Z :=
  if (2^64 - 4095 <=? bv_unsigned r)%Z then Some (2^64 - bv_unsigned r)%Z else None.

Inductive sret : Type := SErr (e : Z) | SVal (v : Z).

Definition no_cc (rsp : resp) : bool :=
  match eff_copies rsp, eff_copyins rsp with [], [] => true | _, _ => false end.

Ltac dec_cc cs ci H := cbn [no_cc eff_copies eff_copyins] in H; destruct cs; [|discriminate H]; destruct ci; [|discriminate H]; cbv iota in H.

Definition dec_plain (ok : Z -> bool) (rsp : resp) : option sret :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ =>
      match errno_of r with
      | Some e => Some (SErr e)
      | None => if ok (bv_unsigned r) then Some (SVal (bv_unsigned r)) else None
      end
  | _ => None
  end else None.

Inductive read_ans : Type := RdErr (e : Z) | RdData (bs : list byte).

Definition dec_read (buf count : Z) (rsp : resp) : option read_ans :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ =>
      match errno_of r with
      | Some e => Some (RdErr e)
      | None => if (bv_unsigned r =? 0)%Z then Some (RdData []) else None
      end
  | mkEffectU r [(a, bs)] [] [] _ _ =>
      if bv_eqb a (Z_to_bv 64 buf) && (1 <=? Z.of_nat (length bs))%Z
         && (Z.of_nat (length bs) <=? count)%Z && (bv_unsigned r =? Z.of_nat (length bs))%Z
      then Some (RdData bs) else None
  | _ => None
  end else None.

Definition dec_count (count : Z) (rsp : resp) : option Z :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ => if (bv_unsigned r =? count)%Z then Some count else None
  | _ => None
  end else None.
Definition dec_write := dec_count.
Definition dec_writev := dec_count.

Definition dec_open : resp -> option sret := dec_plain (fun v => (3 <=? v)%Z && (v <=? 4096)%Z).

Definition dec_close : resp -> option sret := dec_plain (fun v => (v =? 0)%Z).

Definition dec_ioctl : resp -> option sret := dec_plain (fun _ => false).

Definition dec_set_tid (rsp : resp) : option Z :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ =>
      if (0 <? bv_unsigned r)%Z && (bv_unsigned r <? PID_MAX_ENVELOPE)%Z then Some (bv_unsigned r) else None
  | _ => None
  end else None.

Definition dec_exit (rsp : resp) : option Empty_set := None.

Definition dec_brk0 (rsp : resp) : option Z :=
  if no_cc rsp then match rsp with mkEffectU r [] [] [] _ _ => Some (bv_unsigned r) | _ => None end else None.

Definition brk_new_pages (cur req : Z) : option (Z * Z) :=
  let lo := page_round_up_Z cur in let hi := page_round_up_Z req in
  if (lo <? hi)%Z then Some (lo, hi - lo)%Z else None.

Definition zeros_of (p : option (Z * Z)) : list (word * word) :=
  match p with Some (lo, n) => [(wa lo, Z_to_bv 64 n)] | None => [] end.

Inductive brk_ans : Type := BrkGrown | BrkSame.

Definition dec_brk (cur req : Z) (rsp : resp) : option brk_ans :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] zs [] _ _ =>
      if (bv_unsigned r =? cur)%Z && match zs with [] => true | _ => false end then Some BrkSame
      else if (bv_unsigned r =? req)%Z && listNN_eqb zs (zeros_of (brk_new_pages cur req)) then Some BrkGrown
      else None
  | _ => None
  end else None.

Definition CEIL_MIN : Z := 0x7fff7f800000.
Definition CEIL_MAX : Z := 0x7fffff800000.
Definition CEIL_BAND : Z := 0x800000000000.
Definition alloc_ceiling : Z := 0x7fffff800000.

Inductive mmap_ans : Type := MmErr (e : Z) | MmOk (a : Z).

Definition avoids (a n : Z) (avoid : list (Z * Z)) : bool :=
  forallb (fun iv => (a + n <=? fst iv)%Z || (snd iv <=? a)%Z) avoid.

Definition mmap_len (len : Z) : Z := page_round_up_Z len.

Section HC.
Context {HC : HeapCeil}.

Definition mmap_addr_ok (len : Z) (avoid : list (Z * Z)) (a : Z) : bool :=
  (a mod page_size =? 0)%Z && (0 <? a)%Z && (a + mmap_len len <=? hceil)%Z && avoids a (mmap_len len) avoid.

Definition dec_mmap (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ => match errno_of r with Some e => Some (MmErr e) | None => None end
  | mkEffectU r [] [(a, n)] [] _ _ =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end else None.

Definition dec_mmap_none (len : Z) (avoid : list (Z * Z)) (rsp : resp) : option mmap_ans :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ => match errno_of r with Some e => Some (MmErr e) | None => None end
  | mkEffectU r [] [] [(a, n)] _ _ =>
      if bv_eqb a r && bv_eqb n (Z_to_bv 64 (mmap_len len)) && mmap_addr_ok len avoid (bv_unsigned r)
      then Some (MmOk (bv_unsigned r)) else None
  | _ => None
  end else None.

End HC.

Inductive range_ans : Type := RgErr (e : Z) | RgDone (changed : bool).

Definition dec_munmap (addr len : Z) (rsp : resp) : option range_ans :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ =>
      match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | mkEffectU r [] [] [(a, n)] _ _ =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end else None.

Definition dec_mprotect (addr len : Z) (rsp : resp) : option range_ans :=
  if no_cc rsp then match rsp with
  | mkEffectU r [] [] [] _ _ =>
      match errno_of r with Some e => Some (RgErr e) | None => if (bv_unsigned r =? 0)%Z then Some (RgDone false) else None end
  | mkEffectU r [] [(a, n)] [] _ _ =>
      if (bv_unsigned r =? 0)%Z && bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len))
      then Some (RgDone true) else None
  | _ => None
  end else None.

