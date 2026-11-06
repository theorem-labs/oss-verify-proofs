(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan GapsM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkBody.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import DecPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RangeC MemcpyC.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PkBodyAC.
Section WithSegs.
Variable segs : list Segment.

Definition sink (st st1 : sstate) (r : int) : sstate := setpc (setr (clobber st1) X10 (getr st X10)) r.

Definition lit_src_ok (st : sstate) (wnl : list (int * sv * w64)) (kS : int) (n : sv) : bool :=
  match getr st X11, n with
  | VP ks os, VL nw =>
      negb (wt nw) && PrimInt63.leb 1%uint63 (wl nw) && PrimInt63.leb (wl nw) RangeC.NMAX && negb (PrimInt63.eqb ks kS)
      && MemcpyC.range_in segs st wnl ks os (wl nw) false
  | _, _ => false
  end.

Definition no_cells (r : region) : bool := match rg_cells r with IMap.Leaf => true | _ => false end.

Definition pkbody_apply_spec (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st, CtrA.sym_offset (s_regs st) (getr st X10) with
  | Some (r, hargs, wnl, st1), Some (kS, OFF) =>
      match IMap.find kS (s_regs st), CtrA.win_lookup wnl kS with
      | Some rS, Some (lenS, kdS) =>
          let fs := s_facts st in
          let n := getr st X12 in
          if negb (PrimInt63.eqb kS 0%uint63) && weqb kdS (wlit 1%uint63)
             && is_bgnone (rg_bg rS) && PrimInt63.eqb (rg_lo rS) 0%uint63 && rg_w rS && no_cells rS
             && known_leu fs OFF (rg_hi rS) && known_leu fs n (sv_alu ALU_SUB (rg_hi rS) OFF) && known_leu fs (rg_hi rS) lenS
             && ActrA.twin_pat_ok st wnl kS
             && (lit_src_ok st wnl kS n || PkBody.body_src_ok st n)
          then Some [sink st st1 r]
          else None
      | _, _ => None
      end
  | _, _ => None
  end.

Definition ltu_open (c : option bool) : bool := match c with None => true | _ => false end.
Definition ltu_true (c : option bool) : bool := match c with Some true => true | _ => false end.
Definition leu3 (fs : list fact) (a1 b1 a2 b2 a3 b3 : sv) : bool :=
  let c1 := DecPre.DecPre.decide_ltu_c fs b1 a1 in
  let c2 := DecPre.DecPre.decide_ltu_c fs b2 a2 in
  let c3 := DecPre.DecPre.decide_ltu_c fs b3 a3 in
  if ltu_true c1 || ltu_true c2 || ltu_true c3 then false
  else if ltu_open c1 || ltu_open c2 || ltu_open c3 then
    let dc := DecPre.DecPre.mk_dc fs in
    if dec_false (DecPre.DecPre.decide_ltu_fin dc fs c1 b1 a1)
    then if dec_false (DecPre.DecPre.decide_ltu_fin dc fs c2 b2 a2) then dec_false (DecPre.DecPre.decide_ltu_fin dc fs c3 b3 a3) else false
    else false
  else true.
Definition pkbody_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st, CtrA.sym_offset (s_regs st) (getr st X10) with
  | Some (r, hargs, wnl, st1), Some (kS, OFF) =>
      match IMap.find kS (s_regs st), CtrA.win_lookup wnl kS with
      | Some rS, Some (lenS, kdS) =>
          let fs := s_facts st in
          let n := getr st X12 in
          if (if negb (PrimInt63.eqb kS 0%uint63) then if weqb kdS (wlit 1%uint63) then if is_bgnone (rg_bg rS) then if PrimInt63.eqb (rg_lo rS) 0%uint63
              then if rg_w rS then no_cells rS else false else false else false else false else false)
          then if leu3 fs OFF (rg_hi rS) n (sv_alu ALU_SUB (rg_hi rS) OFF) (rg_hi rS) lenS
               then if ActrA.twin_pat_ok st wnl kS
                    then (if (if lit_src_ok st wnl kS n then true else PkBody.body_src_ok st n) then Some [sink st st1 r] else None)
                    else None
               else None
          else None
      | _, _ => None
      end
  | _, _ => None
  end.
Lemma leu3_eq : forall fs a1 b1 a2 b2 a3 b3, leu3 fs a1 b1 a2 b2 a3 b3 = known_leu fs a1 b1 && known_leu fs a2 b2 && known_leu fs a3 b3.
Proof.
  intros. unfold leu3, known_leu. cbv zeta.
  pose proof (DecPre.DecPre.mk_dc_ok fs) as Hdc. set (dc := DecPre.DecPre.mk_dc fs) in *.
  rewrite <- !(DecPre.DecPre.decide_ltu_fin_eq fs dc Hdc).
  destruct (DecPre.DecPre.decide_ltu_c fs b1 a1) as [[|]|], (DecPre.DecPre.decide_ltu_c fs b2 a2) as [[|]|], (DecPre.DecPre.decide_ltu_c fs b3 a3) as [[|]|];
    cbn [ltu_true ltu_open orb DecPre.DecPre.decide_ltu_fin dec_false andb]; try reflexivity;
    repeat match goal with |- context [GapsM.GapsM.decide_ltu_Gx ?i ?g ?f ?x ?y] => destruct (GapsM.GapsM.decide_ltu_Gx i g f x y) as [[|]|] end; reflexivity.
Qed.
Lemma pkbody_apply_eq : forall st, pkbody_apply st = pkbody_apply_spec st.
Proof.
  intros st. unfold pkbody_apply, pkbody_apply_spec.
  destruct (ActrA.acall_pre ActrA.ASTACK None st) as [[[[r hargs] wnl] st1]|]; [|reflexivity].
  destruct (CtrA.sym_offset (s_regs st) (getr st X10)) as [[kS OFF]|]; [|reflexivity].
  destruct (IMap.find kS (s_regs st)) as [rS|]; [|reflexivity]. destruct (CtrA.win_lookup wnl kS) as [[lenS kdS]|]; [|reflexivity].
  cbv zeta. rewrite leu3_eq.
  destruct (negb (PrimInt63.eqb kS 0%uint63)), (weqb kdS (wlit 1%uint63)), (is_bgnone (rg_bg rS)), (PrimInt63.eqb (rg_lo rS) 0%uint63), (rg_w rS), (no_cells rS);
    cbn [andb]; try reflexivity.
  destruct (known_leu _ OFF _), (known_leu _ (getr st X12) _), (known_leu _ (rg_hi rS) lenS); cbn [andb]; try reflexivity.
  destruct (ActrA.twin_pat_ok st wnl kS); [|reflexivity]. destruct (lit_src_ok st wnl kS (getr st X12)), (PkBody.body_src_ok st (getr st X12)); reflexivity.
Qed.
Definition pkbody_c (pc : int) : contract := Contract pc pkbody_apply.

End WithSegs.
End PkBodyAC.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.GapsM.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkBody.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.DecPre.
Import Actr.TwinB.
Import RangeC.TwinB MemcpyC.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan CtrLib.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PkBodyAC.
Section WithSegs.
Variable segs : list Segment.

Definition sink (st st1 : sstate) (r : int) : sstate := setpc (setr (clobber st1) X10 (getr st X10)) r.

Definition lit_src_ok (st : sstate) (wnl : list (int * sv * w64)) (kS : int) (n : sv) : bool :=
  match getr st X11, n with
  | VP ks os, VL nw =>
      negb (wt nw) && PrimInt63.leb 1%uint63 (wl nw) && PrimInt63.leb (wl nw) RangeC.TwinB.RangeC.NMAX && negb (PrimInt63.eqb ks kS)
      && MemcpyC.TwinB.MemcpyC.range_in segs st wnl ks os (wl nw) false
  | _, _ => false
  end.

Definition no_cells (r : region) : bool := match rg_cells r with IMap.Leaf => true | _ => false end.

Definition pkbody_apply_spec (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st, CtrA.sym_offset (s_regs st) (getr st X10) with
  | Some (r, hargs, wnl, st1), Some (kS, OFF) =>
      match IMap.find kS (s_regs st), CtrA.win_lookup wnl kS with
      | Some rS, Some (lenS, kdS) =>
          let fs := s_facts st in
          let n := getr st X12 in
          if negb (PrimInt63.eqb kS 0%uint63) && weqb kdS (wlit 1%uint63)
             && is_bgnone (rg_bg rS) && PrimInt63.eqb (rg_lo rS) 0%uint63 && rg_w rS && no_cells rS
             && known_leu fs OFF (rg_hi rS) && known_leu fs n (sv_alu ALU_SUB (rg_hi rS) OFF) && known_leu fs (rg_hi rS) lenS
             && ActrA.twin_pat_ok st wnl kS
             && (lit_src_ok st wnl kS n || PkBody.body_src_ok st n)
          then Some [sink st st1 r]
          else None
      | _, _ => None
      end
  | _, _ => None
  end.

Definition ltu_open (c : option bool) : bool := match c with None => true | _ => false end.
Definition ltu_true (c : option bool) : bool := match c with Some true => true | _ => false end.
Definition leu3 (fs : list fact) (a1 b1 a2 b2 a3 b3 : sv) : bool :=
  let c1 := DecPre.DecPre.decide_ltu_c fs b1 a1 in
  let c2 := DecPre.DecPre.decide_ltu_c fs b2 a2 in
  let c3 := DecPre.DecPre.decide_ltu_c fs b3 a3 in
  if ltu_true c1 || ltu_true c2 || ltu_true c3 then false
  else if ltu_open c1 || ltu_open c2 || ltu_open c3 then
    let dc := DecPre.DecPre.mk_dc fs in
    if dec_false (DecPre.DecPre.decide_ltu_fin dc fs c1 b1 a1)
    then if dec_false (DecPre.DecPre.decide_ltu_fin dc fs c2 b2 a2) then dec_false (DecPre.DecPre.decide_ltu_fin dc fs c3 b3 a3) else false
    else false
  else true.
Definition pkbody_apply (st : sstate) : option (list sstate) :=
  match ActrA.acall_pre ActrA.ASTACK None st, CtrA.sym_offset (s_regs st) (getr st X10) with
  | Some (r, hargs, wnl, st1), Some (kS, OFF) =>
      match IMap.find kS (s_regs st), CtrA.win_lookup wnl kS with
      | Some rS, Some (lenS, kdS) =>
          let fs := s_facts st in
          let n := getr st X12 in
          if (if negb (PrimInt63.eqb kS 0%uint63) then if weqb kdS (wlit 1%uint63) then if is_bgnone (rg_bg rS) then if PrimInt63.eqb (rg_lo rS) 0%uint63
              then if rg_w rS then no_cells rS else false else false else false else false else false)
          then if leu3 fs OFF (rg_hi rS) n (sv_alu ALU_SUB (rg_hi rS) OFF) (rg_hi rS) lenS
               then if ActrA.twin_pat_ok st wnl kS
                    then (if (if lit_src_ok st wnl kS n then true else PkBody.body_src_ok st n) then Some [sink st st1 r] else None)
                    else None
               else None
          else None
      | _, _ => None
      end
  | _, _ => None
  end.
Lemma leu3_eq : forall fs a1 b1 a2 b2 a3 b3, leu3 fs a1 b1 a2 b2 a3 b3 = known_leu fs a1 b1 && known_leu fs a2 b2 && known_leu fs a3 b3.
Proof.
  intros. unfold leu3, known_leu. cbv zeta.
  pose proof (DecPre.DecPre.mk_dc_ok fs) as Hdc. set (dc := DecPre.DecPre.mk_dc fs) in *.
  rewrite <- !(DecPre.DecPre.decide_ltu_fin_eq fs dc Hdc).
  destruct (DecPre.DecPre.decide_ltu_c fs b1 a1) as [[|]|], (DecPre.DecPre.decide_ltu_c fs b2 a2) as [[|]|], (DecPre.DecPre.decide_ltu_c fs b3 a3) as [[|]|];
    cbn [ltu_true ltu_open orb DecPre.DecPre.decide_ltu_fin dec_false andb]; try reflexivity;
    repeat match goal with |- context [GapsM.GapsM.decide_ltu_Gx ?i ?g ?f ?x ?y] => destruct (GapsM.GapsM.decide_ltu_Gx i g f x y) as [[|]|] end; reflexivity.
Qed.
Lemma pkbody_apply_eq : forall st, pkbody_apply st = pkbody_apply_spec st.
Proof.
  intros st. unfold pkbody_apply, pkbody_apply_spec.
  destruct (ActrA.acall_pre ActrA.ASTACK None st) as [[[[r hargs] wnl] st1]|]; [|reflexivity].
  destruct (CtrA.sym_offset (s_regs st) (getr st X10)) as [[kS OFF]|]; [|reflexivity].
  destruct (IMap.find kS (s_regs st)) as [rS|]; [|reflexivity]. destruct (CtrA.win_lookup wnl kS) as [[lenS kdS]|]; [|reflexivity].
  cbv zeta. rewrite leu3_eq.
  destruct (negb (PrimInt63.eqb kS 0%uint63)), (weqb kdS (wlit 1%uint63)), (is_bgnone (rg_bg rS)), (PrimInt63.eqb (rg_lo rS) 0%uint63), (rg_w rS), (no_cells rS);
    cbn [andb]; try reflexivity.
  destruct (known_leu _ OFF _), (known_leu _ (getr st X12) _), (known_leu _ (rg_hi rS) lenS); cbn [andb]; try reflexivity.
  destruct (ActrA.twin_pat_ok st wnl kS); [|reflexivity]. destruct (lit_src_ok st wnl kS (getr st X12)), (PkBody.body_src_ok st (getr st X12)); reflexivity.
Qed.
Definition pkbody_c (pc : int) : contract := Contract pc pkbody_apply.

End WithSegs.
End PkBodyAC.
End TwinB.
