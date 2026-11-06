(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache.

Module CtrM.
Section WithSegs.
Variable segs : list Segment.

Variable errno_addr : int.

Variable libc_addr : int.

Definition libc_ok (st : sstate) : bool :=
  match do_load segs st (VL (wlit (PrimInt63.add libc_addr 3%uint63))) 1%uint63 false,
        do_load segs st (VL (wlit (PrimInt63.add libc_addr 48%uint63))) 8%uint63 false with
  | inl (Some (VL a)), inl (Some (VL b)) => weqb a wzero && weqb b (wlit 4096%uint63)
  | _, _ => false
  end.

Definition ROOM_LAST : w64 := wlit 11%uint63.
Definition roomcap_apply (st : sstate) : option (list sstate) :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      match heap_A hargs, heap_set_A hargs (VL ROOM_LAST) with
      | Some (VL j), Some hargs' => if wleu j ROOM_LAST then Some [set_ops st (set_op HEAP_ID hargs' (s_ops st))] else None
      | _, _ => None
      end
  | None => None
  end.

Definition roomdrop_apply (st : sstate) : option (list sstate) :=
  match find_op HEAP_ID (s_ops st) with
  | Some hargs =>
      match heap_A hargs, heap_set_A hargs (VL wones) with
      | Some (VL _), Some hargs' => Some [set_ops st (set_op HEAP_ID hargs' (s_ops st))]
      | _, _ => None
      end
  | None => None
  end.

Definition MEMCPY_MAX : Z := 256.

Fixpoint copy_bytes (n : nat) (i : int) (src dst : sv) (st : sstate) : option sstate :=
  match n with
  | O => Some st
  | S n' =>
      match do_load segs st (sv_alu ALU_ADD src (VL (wlit i))) 1%uint63 false with
      | inl (Some v) =>
          match do_store segs st (sv_alu ALU_ADD dst (VL (wlit i))) 1%uint63 v with
          | inl st' => copy_bytes n' (PrimInt63.add i 1%uint63) src dst st'
          | inr _ => None
          end
      | _ => None
      end
  end.

Definition rr_separated (st : sstate) (n : int) : bool :=
  match addr_of (getr st X10) with
  | Some (kd, od) =>
      match addr_of (getr st X11) with
      | Some (ks, os) =>
          negb (PrimInt63.eqb ks kd)
          || match okey od, okey os with
             | Some a, Some b => Z.leb (keyZ a + to_Z n) (keyZ b) || Z.leb (keyZ b + to_Z n) (keyZ a)
             | _, _ => false
             end
      | None =>
          match sym_addr_of (s_regs st) (getr st X11) with
          | Some (ks, _, _) => negb (PrimInt63.eqb ks kd)
          | None => false
          end
      end
  | None => false
  end.

Definition memcpy_rr_apply (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X12 with
  | Some r, VL n =>
      if wt n || negb (Z.leb (to_Z (wl n)) MEMCPY_MAX) || negb (PrimInt63.eqb (wl n) 0%uint63 || rr_separated st (wl n)) then None else
      match copy_bytes (Z.to_nat (to_Z (wl n))) 0%uint63 (getr st X11) (getr st X10) st with
      | Some st1 =>
          match havoc_errno segs errno_addr (clobber st1) with
          | Some st2 => Some [setpc st2 r]
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.

Definition memcpy_blob_apply (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X10, getr st X11 with
  | Some r, VP kd od, VP ks os =>
      if negb (weqb od wzero && weqb os wzero) || PrimInt63.eqb kd ks || PrimInt63.eqb kd 0%uint63 || PrimInt63.eqb ks 0%uint63
      then None else
      match IMap.find kd (s_regs st), IMap.find ks (s_regs st) with
      | Some rd, Some rs =>
          match rg_cells rd, rg_cells rs, rg_bg rs with
          | IMap.Leaf, IMap.Leaf, BGBlob j sh =>
              let n := getr st X12 in
              let fs := s_facts st in
              if PrimInt63.eqb sh 0%uint63 && PrimInt63.eqb (rg_lo rs) 0%uint63 && PrimInt63.eqb (rg_lo rd) 0%uint63 && rg_w rd
                 && known_leu fs n (rg_hi rs) && known_leu fs n (rg_hi rd)
              then
                let st1 := setregs st (IMap.add kd (Region 0%uint63 n true (BGBlob j 0%uint63) IMap.empty) (s_regs st)) in
                match havoc_errno segs errno_addr (clobber st1) with
                | Some st2 => Some [setpc st2 r]
                | None => None
                end
              else None
          | _, _, _ => None
          end
      | _, _ => None
      end
  | _, _, _ => None
  end.

Definition strnlen_apply (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X10, getr st X11 with
  | Some r, VP ks os, VL m =>
      if negb (weqb os wzero) || PrimInt63.eqb ks 0%uint63 then None else
      match IMap.find ks (s_regs st) with
      | Some rs =>
          match rg_cells rs, rg_bg rs with
          | IMap.Leaf, BGBlob j sh =>
              let H := rg_hi rs in
              let fs := s_facts st in
              if PrimInt63.eqb sh 0%uint63 && PrimInt63.eqb (rg_lo rs) 0%uint63
                 && known_ltu fs (VL wzero) H && known_leu fs H (VL m)
              then
                let L := sv_alu ALU_SUB H (VL wone) in
                let st1 := addfact (addfact (addfact (clobber st) (FULt L H)) (FULt L (VL m)))
                                   (FEq (sv_ext false 0%uint63 1%uint63 (VBlob false j L 1%uint63)) (VL wzero)) in
                match havoc_errno segs errno_addr (setr st1 X10 L) with
                | Some st2 => Some [setpc st2 r]
                | None => None
                end
              else None
          | _, _ => None
          end
      | None => None
      end
  | _, _, _ => None
  end.

Variable read_stage : int.
Definition RSTAGE_ID : int := 3%uint63.

Definition dst_offset (R : IMap.t region) (a : sv) : option (int * sv) :=
  match a with
  | VP k o => if weqb o wzero then Some (k, VL wzero) else Some (k, VL o)
  | _ => match sym_addr_of R a with Some (k, _, off) => Some (k, off) | None => None end
  end.

Definition new_hi (fs : list fact) (X n : sv) : sv :=
  match n with
  | VAlu ALU_SUB sz X' => if known_eq fs X' X then sz else sv_alu ALU_ADD X n
  | _ => sv_alu ALU_ADD X n
  end.

Definition memcpy_rstage_apply (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X11 with
  | Some r, VL rs =>
      if negb (weqb rs (wlit read_stage)) then None else
      match dst_offset (s_regs st) (getr st X10), find_op RSTAGE_ID (s_ops st), find_op HEAP_ID (s_ops st) with
      | Some (kb, X), Some [off; n'], Some hargs =>
          match IMap.find kb (s_regs st), heap_find_window hargs (VP kb wzero) with
          | Some rb, Some (_, wlen, _) =>
              match rg_cells rb, (match rg_bg rb with BGBlob j sh => (j, sh) | _ => (0%uint63, 1%uint63) end) with
              | IMap.Leaf, (j, sh) =>
                  let n := getr st X12 in
                  let fs := s_facts st in
                  let hi' := new_hi fs X n in
                  if ((PrimInt63.eqb j 4%uint63 && PrimInt63.eqb sh 0%uint63 && known_eq fs (rg_hi rb) X)
                      || known_eq fs X (VL wzero))
                     && PrimInt63.eqb (rg_lo rb) 0%uint63 && rg_w rb && negb (PrimInt63.eqb kb 0%uint63)
                     && known_eq fs off X && known_eq fs n' n
                     && known_leu fs hi' wlen
                  then
                    let st1 := setregs st (IMap.add kb (Region 0%uint63 hi' true (BGBlob 4%uint63 0%uint63) IMap.empty) (s_regs st)) in
                    let st2 := set_ops st1 (set_op RSTAGE_ID [sv_alu ALU_ADD off n; VL wzero] (s_ops st1)) in
                    match havoc_errno segs errno_addr (clobber st2) with
                    | Some st3 => Some [setpc st3 r]
                    | None => None
                    end
                  else None
              | _, _ => None
              end
          | _, _ => None
          end
      | _, _, _ => None
      end
  | _, _ => None
  end.

Definition B13 : sv := VBlob false 13%uint63 (VL wzero) 8%uint63.
Definition B14 : sv := VBlob false 14%uint63 (VL wzero) 8%uint63.

Definition memcpy_payload_apply (st : sstate) : option (list sstate) :=
  match call_pre st, getr st X10 with
  | Some r, VP kp op =>
      if negb (weqb op wzero) || PrimInt63.eqb kp 0%uint63 then None else
      match dst_offset (s_regs st) (getr st X11), IMap.find kp (s_regs st) with
      | Some (kb, OFF), Some rp =>
          match IMap.find kb (s_regs st) with
          | Some rb =>
              match rg_cells rp, rg_cells rb, rg_bg rb with
              | IMap.Leaf, IMap.Leaf, BGBlob j sh =>
                  let n := getr st X12 in
                  let fs := s_facts st in
                  if PrimInt63.eqb j 4%uint63 && PrimInt63.eqb sh 0%uint63 && PrimInt63.eqb (rg_lo rb) 0%uint63
                     && PrimInt63.eqb (rg_lo rp) 0%uint63 && rg_w rp && negb (PrimInt63.eqb kb kp) && negb (PrimInt63.eqb kb 0%uint63)
                     && fact_lookup fs (is_FEq OFF B14) && fact_lookup fs (is_FEq n B13)
                     && known_leu fs n (rg_hi rp) && known_leu fs OFF (rg_hi rb) && known_leu fs n (sv_alu ALU_SUB (rg_hi rb) OFF)
                  then
                    let st1 := setregs st (IMap.add kp (Region 0%uint63 n false (BGBlob 5%uint63 0%uint63) IMap.empty) (s_regs st)) in
                    match havoc_errno segs errno_addr (clobber st1) with
                    | Some st2 => Some [setpc st2 r]
                    | None => None
                    end
                  else None
              | _, _, _ => None
              end
          | None => None
          end
      | _, _ => None
      end
  | _, _ => None
  end.

Definition roomdrop_c (pc : int) : contract := Contract pc roomdrop_apply.
Definition roomcap_c (pc : int) : contract := Contract pc roomcap_apply.
Definition memcpy_rr_c (pc : int) : contract := Contract pc memcpy_rr_apply.
Definition memcpy_blob_c (pc : int) : contract := Contract pc memcpy_blob_apply.
Definition strnlen_c (pc : int) : contract := Contract pc strnlen_apply.
Definition memcpy_rstage_c (pc : int) : contract := Contract pc memcpy_rstage_apply.
Definition memcpy_payload_c (pc : int) : contract := Contract pc memcpy_payload_apply.

End WithSegs.

End CtrM.
