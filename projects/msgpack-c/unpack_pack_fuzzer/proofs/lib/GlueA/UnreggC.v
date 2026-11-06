(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module UnreggC.

Record ucfg := UCfg {
  u_gva : Z;
  u_n : Z;
  u_mtx : Z;
  u_rgl : Z;
  u_rglv : w64;
  u_got80 : Z;
  u_shmap : int;
  u_hull : Z * Z;
  u_zch : list (Z * Z)
}.

Definition range_untouched (r : region) (lo n : Z) : bool :=
  forallb (fun g => match IMap.find (of_Z g) (rg_cells r) with None => true | Some _ => false end)
          (map (fun i => lo / 8 + Z.of_nat i) (seq 0 (Z.to_nat ((lo + n - 1) / 8 - lo / 8 + 1)))).
Definition lit_cell0 (r : region) (A : Z) (w : w64) : bool :=
  match IMap.find (of_Z (A / 8)) (rg_cells r) with
  | Some gr => existsb (fun c => PrimInt63.eqb (c_idx c) 0%uint63 && PrimInt63.eqb (c_w c) 8%uint63 && sv_eqb (c_v c) (VL w)) (g_cells gr)
  | None => false
  end.
Definition is_bgimage (b : bg) : bool := match b with BGImage => true | _ => false end.

Definition unregg_pre_b (C : ucfg) (st : sstate) : bool :=
  match IMap.find 0%uint63 (s_regs st) with
  | Some r0 =>
      sv_eqb (getr st X10) (VL (Z2w (u_gva C))) && sv_eqb (getr st X11) (VL (Z2w (u_n C)))
      && is_bgimage (rg_bg r0)
      && range_untouched r0 (u_gva C) (64 * u_n C) && negb (in_priv_b (s_priv st) (of_Z (u_gva C)) (of_Z (64 * u_n C)))

      && lit_cell0 r0 (u_mtx C) wzero && lit_cell0 r0 (u_rgl C) (u_rglv C)
      && match find_op (u_shmap C) (s_ops st) with Some [] => true | _ => false end
  | None => false
  end.

Definition hull_view_ok (C : ucfg) (fs : list fact) (k : int) (r : region) : bool :=
  negb (ActrA.view_I fs k r) ||
  match ActrA.zero_view r, ActrA.find_pin fs k with
  | Some hs, Some a =>
      let lo := w2Z a + keyZ (rg_lo r) in let hi := w2Z a + hs in
      Z.leb hi (fst (u_hull C)) || Z.leb (snd (u_hull C)) lo || existsb (fun c => Z.leb (fst c) lo && Z.leb hi (fst c + snd c)) (u_zch C)
  | _, _ => false
  end.

Definition GSH_ID : int := 17%uint63.
Definition hull_views_ok (C : ucfg) (st : sstate) : bool :=
  IMap.forallb (hull_view_ok C (s_facts st)) (s_regs st)
  && match find_op GSH_ID (s_ops st) with None => true | Some _ => false end.

Definition unregg_apply (C : ucfg) (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      if unregg_pre_b C st && hull_views_ok C st then
        let st2 := clobber st1 in
        let (x, st3) := fresh st2 in
        Some [setpc (setr st3 X10 (VP x wzero)) r]
      else None
  | None => None
  end.

Definition unregg_c (C : ucfg) (pc : int) : contract := Contract pc (unregg_apply C).

Definition CFG_ASAN : ucfg := UCfg 0xd5e90 21 0xd7370 0xd72d0 (wlit 0x0101010000000001%uint63) 0xd1538 10%uint63 (0x7fffc58c, 0x7fffc66c)
  [(0x7fffc58c, 4); (0x7fffc590, 8); (0x7fffc5a0, 4); (0x7fffc5a4, 16); (0x7fffc5b4, 4); (0x7fffc5b8, 20); (0x7fffc5cc, 4); (0x7fffc5d0, 16); (0x7fffc5e0, 4);
   (0x7fffc5e4, 8); (0x7fffc5f4, 8); (0x7fffc604, 8); (0x7fffc614, 8); (0x7fffc624, 4); (0x7fffc62c, 4); (0x7fffc630, 8); (0x7fffc640, 4); (0x7fffc644, 8);
   (0x7fffc654, 4); (0x7fffc658, 16); (0x7fffc668, 4)].

End UnreggC.

Module TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import Actr.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan CtrLib.
Open Scope Z_scope.

Module UnreggC.

Record ucfg := UCfg {
  u_gva : Z;
  u_n : Z;
  u_mtx : Z;
  u_rgl : Z;
  u_rglv : w64;
  u_got80 : Z;
  u_shmap : int;
  u_hull : Z * Z;
  u_zch : list (Z * Z)
}.

Definition range_untouched (r : region) (lo n : Z) : bool :=
  forallb (fun g => match IMap.find (of_Z g) (rg_cells r) with None => true | Some _ => false end)
          (map (fun i => lo / 8 + Z.of_nat i) (seq 0 (Z.to_nat ((lo + n - 1) / 8 - lo / 8 + 1)))).
Definition lit_cell0 (r : region) (A : Z) (w : w64) : bool :=
  match IMap.find (of_Z (A / 8)) (rg_cells r) with
  | Some gr => existsb (fun c => PrimInt63.eqb (c_idx c) 0%uint63 && PrimInt63.eqb (c_w c) 8%uint63 && sv_eqb (c_v c) (VL w)) (g_cells gr)
  | None => false
  end.
Definition is_bgimage (b : bg) : bool := match b with BGImage => true | _ => false end.

Definition unregg_pre_b (C : ucfg) (st : sstate) : bool :=
  match IMap.find 0%uint63 (s_regs st) with
  | Some r0 =>
      sv_eqb (getr st X10) (VL (Z2w (u_gva C))) && sv_eqb (getr st X11) (VL (Z2w (u_n C)))
      && is_bgimage (rg_bg r0)
      && range_untouched r0 (u_gva C) (64 * u_n C) && negb (in_priv_b (s_priv st) (of_Z (u_gva C)) (of_Z (64 * u_n C)))

      && lit_cell0 r0 (u_mtx C) wzero && lit_cell0 r0 (u_rgl C) (u_rglv C)
      && match find_op (u_shmap C) (s_ops st) with Some [] => true | _ => false end
  | None => false
  end.

Definition hull_view_ok (C : ucfg) (fs : list fact) (k : int) (r : region) : bool :=
  negb (ActrA.view_I fs k r) ||
  match ActrA.zero_view r, ActrA.find_pin fs k with
  | Some hs, Some a =>
      let lo := w2Z a + keyZ (rg_lo r) in let hi := w2Z a + hs in
      Z.leb hi (fst (u_hull C)) || Z.leb (snd (u_hull C)) lo || existsb (fun c => Z.leb (fst c) lo && Z.leb hi (fst c + snd c)) (u_zch C)
  | _, _ => false
  end.

Definition GSH_ID : int := 17%uint63.
Definition hull_views_ok (C : ucfg) (st : sstate) : bool :=
  IMap.forallb (hull_view_ok C (s_facts st)) (s_regs st)
  && match find_op GSH_ID (s_ops st) with None => true | Some _ => false end.

Definition unregg_apply (C : ucfg) (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st with
  | Some (r, hargs, wl, st1) =>
      if unregg_pre_b C st && hull_views_ok C st then
        let st2 := clobber st1 in
        let (x, st3) := fresh st2 in
        Some [setpc (setr st3 X10 (VP x wzero)) r]
      else None
  | None => None
  end.

Definition unregg_c (C : ucfg) (pc : int) : contract := Contract pc (unregg_apply C).

Definition CFG_ASAN : ucfg := UCfg 0xd7fb0 24 0xd9530 0xd9490 (wlit 0x0101010000000001%uint63) 0xd3650 10%uint63 (0x7fffc5a0, 0x7fffc6a0)
  [(0x7fffc5a0, 4); (0x7fffc5a4, 8); (0x7fffc5b4, 4); (0x7fffc5b8, 16); (0x7fffc5c8, 4); (0x7fffc5cc, 20); (0x7fffc5e0, 4); (0x7fffc5e4, 16); (0x7fffc5f4, 4);
   (0x7fffc5f8, 8); (0x7fffc608, 12); (0x7fffc614, 16); (0x7fffc624, 4); (0x7fffc628, 8); (0x7fffc638, 8); (0x7fffc648, 8); (0x7fffc658, 4); (0x7fffc660, 4);
   (0x7fffc664, 8); (0x7fffc674, 4); (0x7fffc678, 8); (0x7fffc688, 4); (0x7fffc68c, 16); (0x7fffc69c, 4)].

End UnreggC.
End TwinB.
