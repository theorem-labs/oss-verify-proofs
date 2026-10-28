(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BeapSecret.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BLPropExec BMState BMem BExec BITree BLNodes BDecode.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim BMonad BSTree BMalloc BMallocCtrl.
Import ListNotations.
Import BITree.Exc.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.
Open Scope mspec_scope.

Record PState := mkPS {
  ps_m   : mstate;
  ps_brk : Z;
  ps_fa  : Z * Z;
  ps_so  : unit
}.
Definition set_m (v : mstate) (s : PState) := mkPS v (ps_brk s) (ps_fa s) (ps_so s).
Definition set_brk_ps (v : Z) (s : PState) := mkPS (ps_m s) v (ps_fa s) (ps_so s).
Definition set_fa_ps (v : Z * Z) (s : PState) := mkPS (ps_m s) (ps_brk s) v (ps_so s).
Definition set_so_ps (v : unit) (s : PState) := mkPS (ps_m s) (ps_brk s) (ps_fa s) v.

Local Notation MP := (BMonad.M PState).

Definition neg_errno (e : Z) : Z := 2^64 - e.

Definition MAP_FIXED_Z : Z := 16.

Inductive fixed_ans : Type := FxKept (e : Z) | FxDone | FxLost (e : Z).
Definition dec_mmap_fixed (addr len : Z) (rsp : resp) : option fixed_ans :=
  if no_cc rsp then
  match rsp with
  | mkEffectU r [] [] [] _ _ => match errno_of r with Some e => Some (FxKept e) | None => None end
  | mkEffectU r [] [] [(a, n)] _ _ =>
      if bv_eqb a (Z_to_bv 64 addr) && bv_eqb n (Z_to_bv 64 (mmap_len len)) then
        match errno_of r with
        | Some e => Some (FxLost e)
        | None => if bv_eqb r (Z_to_bv 64 addr) then Some FxDone else None
        end
      else None
  | _ => None
  end else None.

Definition dec_mprotect_rw (addr len : Z) (rsp : resp) : option range_ans :=
  match dec_mprotect addr len rsp with
  | Some (RgErr e) => if e =? ENOSYS then None else Some (RgErr e)
  | Some (RgDone true) => Some (RgDone true)
  | _ => None
  end.

Section HC.
Context {HC : HeapCeil}.

Definition ev_step (e : ev) : MP Z :=
  match e with
  | EBrk req =>
      if req =? 0 then
        (r <- msys (NBrk 0) dec_brk0 ;; mupd (set_brk_ps r) ;;; mret r)
      else
        (s <- mget ;;
         a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with
         | BrkGrown => mupd (set_brk_ps req) ;;; mret req
         | BrkSame => mret (ps_brk s)
         end)
  | EMmap addr len prot flags =>
      if negb (Z.land flags MAP_FIXED_Z =? 0) then
        (a <- msys (NMmap addr len prot flags) (dec_mmap_fixed addr len) ;;
         mret match a with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end)
      else if prot =? 0 then
        (a <- msys (NMmap addr len prot flags) (dec_mmap_none len []) ;;
         mret match a with MmErr e => neg_errno e | MmOk x => x end)
      else
        (a <- msys (NMmap addr len prot flags) (dec_mmap len []) ;;
         mret match a with MmErr e => neg_errno e | MmOk x => x end)
  | EMunmap addr len =>
      a <- msys (NMunmap addr len) (dec_munmap addr len) ;;
      mret match a with RgErr e => neg_errno e | RgDone _ => 0 end
  | EMprotect addr len prot =>
      a <- msys (NMprotect addr len prot) (dec_mprotect_rw addr len) ;;
      mret match a with RgErr e => neg_errno e | RgDone _ => 0 end
  | EPeek _ _ _ => munr
  | EUndef _ => munr
  end.

Fixpoint membed {R} (t : stree ev Z R) : MP R :=
  match t with
  | SRet r => mret r
  | SVis e k => z <- ev_step e ;; membed (k z)
  end.

Definition bptr : Type := (cptr * Z)%type.

Definition fresh_off (cs : mstate) (slot : cptr) (n : Z) : Z :=
  match (s_slots cs) !! slot with
  | Some (g, idx) =>
      let mr := get_meta_rec cs g in
      fold_off (Z.land (c_mmap_counter (s_ctx cs)) 255) ((get_stride mr - IB - n) / UNIT)
  | None => 0
  end.

Definition raw_malloc (n : Z) : MP (option bptr) :=
  s <- mget ;;
  '(st', p) <- membed (cmalloc (ps_m s) n) ;;
  mupd (set_m st') ;;;
  mret (match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end).
Definition raw_free (p : bptr) : MP unit :=
  s <- mget ;;
  st' <- membed (cfree (ps_m s) (Some (fst p))) ;;
  mupd (set_m st').
End HC.

Definition ptr_addr (s : PState) (p : bptr) : Z := conc (ps_m s) (fst p) + UNIT * snd p.

Definition rband (ceil : Z) : Z * Z := (ceil, CEIL_BAND).

Section PSInit.
Context {HC : HeapCeil} {HSEC : HeapSecret}.
Definition ps_init (reserved : list (Z * Z)) : PState :=
  mkPS (strip (minit hsecret (rband hceil :: reserved))) 0 (0, 0) tt.
End PSInit.

Definition sceil (cs : mstate) : Z :=
  match s_reserved cs with (c, _) :: _ => c | [] => alloc_ceiling end.

Definition reservedZ (segs : list Segment) : list (Z * Z) :=
  map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) (segments_reserved segs).
