(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import W64 ITrie FxSpec FxInstr FxState FxMem FxExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Rel.
Variable segs : list Segment.
Variable IM : fimage.
Variable rho : int -> word.

(* [comment removed for export] *)
Definition sx32 (x : word) : word := sext 64 (bv_extract 0 32 x).
Definition hi32 (x : word) : word := sext 64 (bv_extract 32 32 x).
Definition b5 (x : word) : word := zext 64 (bv_extract 40 8 x).
Definition dvk (k : int) (x w : word) : word :=
  if (k =? 1)%uint63 then bv_add (bv_opp x) w
  else if (k =? 2)%uint63 then sx32 (bv_add x w)
  else if (k =? 3)%uint63 then hi32 (bv_add x w)
  else if (k =? 4)%uint63 then sx32 (bv_add (bv_opp x) w)
  else if (k =? 5)%uint63 then b5 (bv_add x w)
  else if (k =? 6)%uint63 then alu64 ALU_SRL (bv_add x w) (Z_to_bv 64 12)
  else if (k =? 7)%uint63 then alu64 ALU_SLL (bv_add x w) (Z_to_bv 64 3)
  else bv_add x w.
Definition dv (v : fval) : word := dvk (vkind (vtag v)) (rho (vbase (vtag v))) (wbv (vw v)).

(* [comment removed for export] *)
Definition adr (t : int) (z : Z) : word := bv_add (rho t) (Z_to_bv 64 z).

(* [comment removed for export] *)
Definition wbytes8 (w : word) : list byte := Z_to_le_bytes 8 (bv_unsigned w).

(* [comment removed for export] *)
Definition fseg_ok (sg : fseg) : Prop :=
  exists seg, In seg segs
    /\ Z.of_N (seg_base seg) = to_Z (sg_base sg) /\ Z.of_N (seg_size seg) = to_Z (sg_size sg)
    /\ seg_bytes seg = [sg_hex sg]
    /\ seg_readable seg = true /\ seg_writable seg = sg_wr sg
    /\ to_Z (sg_base sg) mod 4096 = 0 /\ to_Z (sg_size sg) mod 4096 = 0
    /\ to_Z (sg_base sg) + to_Z (sg_size sg) <= 2 ^ 62
    /\ (forall a, to_Z (sg_base sg) <= a < to_Z (sg_base sg) + to_Z (sg_size sg) ->
                  find_segment segs a 1 = Some seg).
Definition image_ok : Prop := Forall fseg_ok IM.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition slot_ok (m : word -> option byte) (a : word) (s : slot) : Prop :=
  match s with
  | SK b => rview segs m a = Some (Z_to_bv 8 (to_Z b))
  | SV v j => rview segs m a = nth_error (wbytes8 (dv v)) (Z.to_nat (to_Z j))
  | SU => True
  end.

(* [comment removed for export] *)
Definition page_ok (m : word -> option byte) (t pn : int) (B : Z) (p : page) : Prop :=
  (pg_wr p = true ->
     forall j, 0 <= j < B -> wview segs m (adr t (to_Z pn * 4096 + j)) <> None)
  /\ (forall ci v, 0 <= to_Z ci < B / 8 -> cell_at IM p pn ci = Some v ->
        forall j, (j < 8)%nat ->
          rview segs m (adr t (to_Z pn * 4096 + to_Z ci * 8 + Z.of_nat j)) = nth_error (wbytes8 (dv v)) j)
  /\ (forall ci sl, 0 <= to_Z ci -> to_Z ci * 8 < B -> iget ci (pg_cells p) = Some (CB sl) ->
        forall j : int, 0 <= to_Z j < 8 ->
          (to_Z ci * 8 + to_Z j < B -> slot_ok m (adr t (to_Z pn * 4096 + to_Z ci * 8 + to_Z j)) (sget j sl))
          /\ (B <= to_Z ci * 8 + to_Z j -> sget j sl = SU))
  /\ (forall ci, 0 <= to_Z ci -> to_Z ci * 8 < B < to_Z ci * 8 + 8 -> cell_at IM p pn ci = None).

(* [comment removed for export] *)
Definition blim (rg : region) (pn : int) : Z := Z.min 4096 (to_Z (rg_len rg) - to_Z pn * 4096).
Definition clim (rg : region) (pn : int) : Z := blim rg pn / 8.

(* [comment removed for export] *)
Definition rkind_ok (t : int) (k : rkind) : Prop :=
  match k with
  | RK_plain => True
  | RK_shadow p => to_Z p < to_Z t
                   /\ bv_unsigned (rho t) = bv_unsigned (rho p) / 8 + to_Z shadow_K
  end.

Definition region_ok (t : int) (rg : region) : Prop :=
  to_Z t < 2 ^ 60                                   (* [comment removed for export] *)
  /\ to_Z (rg_len rg) <= 2 ^ 62
  /\ bv_unsigned (rho t) + to_Z (rg_len rg) < 2 ^ 63
  /\ (t <> 0%uint63 -> 0 < bv_unsigned (rho t) + to_Z (rg_lo rg))
  /\ bv_unsigned (rho t) mod 2 ^ (to_Z (rg_align rg)) = 0
  /\ to_Z (rg_clo rg) <= bv_unsigned (rho t) <= to_Z (rg_chi rg)    (* [comment removed for export] *)
  /\ rkind_ok t (rg_kind rg).                                       (* [comment removed for export] *)

(* [comment removed for export] *)
Definition regions_sep (M : itrie region) : Prop :=
  forall t t' rg rg', t <> t' -> iget t M = Some rg -> iget t' M = Some rg' ->
    bv_unsigned (rho t) + to_Z (rg_len rg) <= bv_unsigned (rho t') + to_Z (rg_lo rg')
    \/ bv_unsigned (rho t') + to_Z (rg_len rg') <= bv_unsigned (rho t) + to_Z (rg_lo rg).

Definition mem_ok (M : itrie region) (m : word -> option byte) : Prop :=
  (forall t rg, iget t M = Some rg ->
      region_ok t rg
      /\ forall pn p, to_Z pn < 2 ^ 50 -> page_at IM rg t pn = Some p ->
           page_ok m t pn (blim rg pn) p
           /\ to_Z (rg_lo rg) <= to_Z pn * 4096 /\ to_Z pn * 4096 < to_Z (rg_len rg))
  /\ regions_sep M.

(* [comment removed for export] *)
Record R (F : fstate) (ms : machine_state) : Prop := mkR {
  R_pc   : ms_pc_val ms = Z_to_bv 64 (to_Z (f_pc F));
  R_regs : forall r : reg, Sem.rget (core_of ms) r = dv (FxState.rget F (ireg r));
  R_svc  : ms_svc_pending ms = None;
  R_resv : ms_resv ms = option_map dv (f_resv F);
  R_mem  : mem_ok (f_mem F) (ms_mem ms)
}.

(* [comment removed for export] *)
Definition code_ok (code : itrie finstr) : Prop :=
  forall pc fi, iget pc code = Some fi -> build_entry segs (to_Z pc) = Some fi.
End Rel.
