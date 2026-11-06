(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module GshC.
Definition GSH_ID : int := 17%uint63.
Definition SHMAP_ID : int := 10%uint63.
Definition tab_t : Type := list (Z * Z * Z).

Record gcfg := GCfg {
  g_tab : tab_t;
  g_lo : Z;
  g_hi : Z;
  g_slot : Z
}.
Definition GSH_TAB_ASAN : tab_t :=
  [(2147468684, 1, 7); (2147468688, 2, 0); (2147468690, 1, 3); (2147468696, 9, 0); (2147468705, 1, 3); (2147468708, 8, 0); (2147468716, 1, 3); (2147468724, 1, 0); (2147468728, 14, 0); (2147468748, 1, 0); (2147468749, 1, 7); (2147468752, 10, 0); (2147468762, 1, 3); (2147468768, 1, 0); (2147468769, 1, 2); (2147468772, 2, 0); (2147468774, 1, 2); (2147468780, 10, 0); (2147468790, 1, 4); (2147468796, 10, 0); (2147468806, 1, 4); (2147468812, 10, 0); (2147468822, 1, 2); (2147468828, 9, 0); (2147468837, 1, 4); (2147468840, 5, 0); (2147468845, 1, 2); (2147468848, 2, 0); (2147468850, 1, 2); (2147468856, 9, 0); (2147468865, 1, 2); (2147468868, 2, 0); (2147468870, 1, 2); (2147468876, 10, 0); (2147468888, 8, 0); (2147468896, 1, 5); (2147468904, 1, 6)].
Definition CFG_ASAN : gcfg := GCfg GSH_TAB_ASAN 0x22c80 0x23360 0xd32b8.

Definition GSH_VIDS : list int := [17%uint63; 1%uint63].
Definition GSH_ZERO_WINS_ASAN : list (int * int) :=
  [(2147468688%uint63, 2147468690%uint63); (2147468696%uint63, 2147468705%uint63); (2147468708%uint63, 2147468716%uint63); (2147468724%uint63, 2147468725%uint63); (2147468728%uint63, 2147468742%uint63); (2147468748%uint63, 2147468749%uint63); (2147468752%uint63, 2147468762%uint63); (2147468768%uint63, 2147468769%uint63); (2147468772%uint63, 2147468774%uint63); (2147468780%uint63, 2147468790%uint63); (2147468796%uint63, 2147468806%uint63); (2147468812%uint63, 2147468822%uint63); (2147468828%uint63, 2147468837%uint63); (2147468840%uint63, 2147468845%uint63); (2147468848%uint63, 2147468850%uint63); (2147468856%uint63, 2147468865%uint63); (2147468868%uint63, 2147468870%uint63); (2147468876%uint63, 2147468886%uint63); (2147468888%uint63, 2147468896%uint63)].
Fixpoint gsh_byte (tab : tab_t) (s : Z) : option Z :=
  match tab with
  | [] => None
  | (a, n, v) :: t => if (a <=? s) && (s <? a + n) then Some v else gsh_byte t s
  end.

Fixpoint gsh_grans (tab : tab_t) (fuel : nat) (G hi : Z) : bool :=
  match fuel with
  | O => true
  | S f =>
      match gsh_byte tab (2147450880 + G) with
      | Some v => ((v =? 0) || ((Z.min (8 * G + 8) hi - 8 * G <=? v) && (v <=? 7))) && gsh_grans tab f (G + 1) hi
      | None => false
      end
  end.
Definition gsh_unpoisoned (tab : tab_t) (lo len : Z) : bool :=
  (0 <? len) && (0 <=? lo) && gsh_grans tab (Z.to_nat ((lo + len - 1) / 8 - lo / 8 + 1)) (lo / 8) (lo + len).

Definition lit_gsh (C : gcfg) (st : sstate) (a : w64) (len : int) : bool :=
  let A := to_Z (wl a) in
  negb (wt a) && (g_lo C <=? A) && (A + to_Z len + 8 <=? g_hi C) && gsh_unpoisoned (g_tab C) A (to_Z len)
  && match find_op GSH_ID (s_ops st) with Some [] => true | _ => false end
  && match find_op SHMAP_ID (s_ops st) with Some [] => true | _ => false end.

Section WithSegs.
Variable segs : list Segment.

Fixpoint scan_nul (fuel : nat) (st : sstate) (a i : int) : option int :=
  match fuel with
  | O => None
  | S f => match do_load segs st (VL (wlit (PrimInt63.add a i))) 1%uint63 false with
           | inl (Some (VL z)) => if weqb z wzero then Some i else scan_nul f st a (PrimInt63.add i 1%uint63)
           | _ => None
           end
  end.

Fixpoint lit_loads (fuel : nat) (st : sstate) (a : int) : bool :=
  match fuel with
  | O => true
  | S f => match do_load segs st (VL (wlit a)) 1%uint63 false with
           | inl (Some (VL _)) => lit_loads f st (PrimInt63.add a 1%uint63)
           | _ => false
           end
  end.

Definition gstr (C : gcfg) (st : sstate) (a : w64) : option int :=
  let A := to_Z (wl a) in
  if negb (wt a) && (g_lo C <=? A) && (A <? g_hi C) then
    match scan_nul 64 st (wl a) 0%uint63 with
    | Some len =>
        let n := to_Z len + 1 in
        let e := A + n in
        if (e + 8 <=? g_hi C) && lit_loads (Z.to_nat ((- e) mod 8)) st (PrimInt63.add (wl a) (PrimInt63.add len 1%uint63)) && gsh_unpoisoned (g_tab C) A n
           && match find_op GSH_ID (s_ops st) with Some [] => true | _ => false end
           && match find_op SHMAP_ID (s_ops st) with Some [] => true | _ => false end
        then Some len else None
    | None => None
    end
  else None.
End WithSegs.
End GshC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module GshC.
Definition GSH_ID : int := 17%uint63.
Definition SHMAP_ID : int := 10%uint63.
Definition tab_t : Type := list (Z * Z * Z).

Record gcfg := GCfg {
  g_tab : tab_t;
  g_lo : Z;
  g_hi : Z;
  g_slot : Z
}.

Definition GSH_TAB_ASAN : tab_t :=
  [(2147468704, 1, 7); (2147468708, 2, 0); (2147468710, 1, 3); (2147468716, 9, 0); (2147468725, 1, 3); (2147468728, 8, 0); (2147468736, 1, 3); (2147468744, 1, 0); (2147468748, 14, 0); (2147468768, 1, 0); (2147468769, 1, 7); (2147468772, 10, 0); (2147468782, 1, 3); (2147468788, 1, 0); (2147468789, 1, 2); (2147468792, 2, 0); (2147468794, 1, 2); (2147468800, 13, 0); (2147468813, 1, 1); (2147468820, 9, 0); (2147468829, 1, 7); (2147468836, 1, 0); (2147468837, 1, 4); (2147468840, 2, 0); (2147468842, 1, 4); (2147468848, 10, 0); (2147468858, 1, 4); (2147468864, 10, 0); (2147468874, 1, 2); (2147468880, 9, 0); (2147468889, 1, 4); (2147468892, 5, 0); (2147468897, 1, 2); (2147468900, 2, 0); (2147468902, 1, 2); (2147468908, 9, 0); (2147468917, 1, 2); (2147468920, 2, 0); (2147468922, 1, 2); (2147468928, 10, 0); (2147468940, 8, 0); (2147468948, 1, 5); (2147468956, 1, 6)].
Definition CFG_ASAN : gcfg := GCfg GSH_TAB_ASAN 0x22d00 0x23500 0xd53d0.

Definition GSH_VIDS : list int := [17%uint63; 1%uint63].
Definition GSH_ZERO_WINS_ASAN : list (int * int) :=
  [(2147468708%uint63, 2147468710%uint63); (2147468716%uint63, 2147468725%uint63); (2147468728%uint63, 2147468736%uint63); (2147468744%uint63, 2147468745%uint63); (2147468748%uint63, 2147468762%uint63); (2147468768%uint63, 2147468769%uint63); (2147468772%uint63, 2147468782%uint63); (2147468788%uint63, 2147468789%uint63); (2147468792%uint63, 2147468794%uint63); (2147468800%uint63, 2147468813%uint63); (2147468820%uint63, 2147468829%uint63); (2147468836%uint63, 2147468837%uint63); (2147468840%uint63, 2147468842%uint63); (2147468848%uint63, 2147468858%uint63); (2147468864%uint63, 2147468874%uint63); (2147468880%uint63, 2147468889%uint63); (2147468892%uint63, 2147468897%uint63); (2147468900%uint63, 2147468902%uint63); (2147468908%uint63, 2147468917%uint63); (2147468920%uint63, 2147468922%uint63); (2147468928%uint63, 2147468938%uint63); (2147468940%uint63, 2147468948%uint63)].
Fixpoint gsh_byte (tab : tab_t) (s : Z) : option Z :=
  match tab with
  | [] => None
  | (a, n, v) :: t => if (a <=? s) && (s <? a + n) then Some v else gsh_byte t s
  end.

Fixpoint gsh_grans (tab : tab_t) (fuel : nat) (G hi : Z) : bool :=
  match fuel with
  | O => true
  | S f =>
      match gsh_byte tab (2147450880 + G) with
      | Some v => ((v =? 0) || ((Z.min (8 * G + 8) hi - 8 * G <=? v) && (v <=? 7))) && gsh_grans tab f (G + 1) hi
      | None => false
      end
  end.
Definition gsh_unpoisoned (tab : tab_t) (lo len : Z) : bool :=
  (0 <? len) && (0 <=? lo) && gsh_grans tab (Z.to_nat ((lo + len - 1) / 8 - lo / 8 + 1)) (lo / 8) (lo + len).

Definition lit_gsh (C : gcfg) (st : sstate) (a : w64) (len : int) : bool :=
  let A := to_Z (wl a) in
  negb (wt a) && (g_lo C <=? A) && (A + to_Z len + 8 <=? g_hi C) && gsh_unpoisoned (g_tab C) A (to_Z len)
  && match find_op GSH_ID (s_ops st) with Some [] => true | _ => false end
  && match find_op SHMAP_ID (s_ops st) with Some [] => true | _ => false end.

Section WithSegs.
Variable segs : list Segment.

Fixpoint scan_nul (fuel : nat) (st : sstate) (a i : int) : option int :=
  match fuel with
  | O => None
  | S f => match do_load segs st (VL (wlit (PrimInt63.add a i))) 1%uint63 false with
           | inl (Some (VL z)) => if weqb z wzero then Some i else scan_nul f st a (PrimInt63.add i 1%uint63)
           | _ => None
           end
  end.

Fixpoint lit_loads (fuel : nat) (st : sstate) (a : int) : bool :=
  match fuel with
  | O => true
  | S f => match do_load segs st (VL (wlit a)) 1%uint63 false with
           | inl (Some (VL _)) => lit_loads f st (PrimInt63.add a 1%uint63)
           | _ => false
           end
  end.

Definition gstr (C : gcfg) (st : sstate) (a : w64) : option int :=
  let A := to_Z (wl a) in
  if negb (wt a) && (g_lo C <=? A) && (A <? g_hi C) then
    match scan_nul 64 st (wl a) 0%uint63 with
    | Some len =>
        let n := to_Z len + 1 in
        let e := A + n in
        if (e + 8 <=? g_hi C) && lit_loads (Z.to_nat ((- e) mod 8)) st (PrimInt63.add (wl a) (PrimInt63.add len 1%uint63)) && gsh_unpoisoned (g_tab C) A n
           && match find_op GSH_ID (s_ops st) with Some [] => true | _ => false end
           && match find_op SHMAP_ID (s_ops st) with Some [] => true | _ => false end
        then Some len else None
    | None => None
    end
  else None.
End WithSegs.
End GshC.
End TwinB.
