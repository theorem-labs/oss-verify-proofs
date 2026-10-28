(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The library interface the ubsan driver walks use (Pm6DrvE_u5, Pm6DrvFW_u5, Pm6DrvLibL_u5), in place of the plain
   record lib_iface_ok_fp. The ubsan library call consumes a payload predicate (LibContractU.LCU.lib_call_okU), so
   the record carries that predicate as a field and a library call needs it for the payload. It has
   lib_iface_ok_fp's four parameters, and lsu_init / lsu_frame have liof_init / liof_frame's arguments and types. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec StoreOk ShapeAlg SpinAlg HeapIface LibIface LibIfaceFp.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.Lib Require Import LibContractU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Record lib_iface_ok_u (Lay : lib_layout) (scfg : SpuriousCfg) (HI : heap_iface) (LSt : lib_statics) : Type := LIOU {
  lsu_phi : list byte -> Prop;
  lsu_ok : LCU.lib_iface_okU Lay scfg HI LSt lsu_phi
}.

Definition lsu_init (Lay : lib_layout) (scfg : SpuriousCfg) (HI : heap_iface) (LSt : lib_statics)
    (H : lib_iface_ok_u Lay scfg HI LSt) : lib_statics_init Lay LSt :=
  LCU.liou_init _ _ _ _ _ (lsu_ok _ _ _ _ H).

Definition lsu_frame (Lay : lib_layout) (scfg : SpuriousCfg) (HI : heap_iface) (LSt : lib_statics)
    (H : lib_iface_ok_u Lay scfg HI LSt) : lib_statics_frame Lay LSt :=
  LCU.liou_frame _ _ _ _ _ (lsu_ok _ _ _ _ H).
