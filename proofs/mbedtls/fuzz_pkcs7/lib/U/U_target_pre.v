(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From LinuxProcessSemantics.LinuxProcessSem Require Import Fs.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec StoreOk BBFrame MallocDefs ShapeX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_enframe_base U_world.
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_target_pre () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.fst"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.snd"].


Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition hdr_b0 (content : list byte) : Z := bv_unsigned (nth 0 content (Z_to_bv 8 0)).
Definition hdr_b1 (content : list byte) : Z := bv_unsigned (nth 1 content (Z_to_bv 8 0)).
Definition hdr_cfg (content : list byte) : Z := hdr_b0 content + 256 * hdr_b1 content.
Definition hdr_cfglen (content : list byte) : Z := hdr_cfg content mod 32768.
Definition hdr_paylen (content : list byte) : Z := Z.of_nat (length content) - 6 - hdr_cfglen content.

(* [comment removed for export] *)
Definition stack_writableZ (M : word -> option byte) (sp0 : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_target_pre ()) "Pd,$0.Pm,$1.P,(2.=R2.)P,(2.(3.R3.(4.R2.))+800000.)(5.$6.(7.$8.O2.(9.&40.(3.(:.O1.+800000.)R4.))R3.)$;.)")
(* [comment removed for export] *).

Record target_pre (sp0 gm area brkv mas tid : Z) (content : list byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := TARGET_PRE {
  (* [comment removed for export] *)
  tp_ra : getr R 1 = Z_to_bv 64 0x1d3c0;
  tp_sp : getr R 2 = Z_to_bv 64 (sp0 - 128);
  tp_gp : getr R 3 = Z_to_bv 64 0x10800;
  tp_tp : getr R 4 = Z_to_bv 64 0x5d0c8;
  tp_a0 : getr R 10 = Z_to_bv 64 (gm + 34);                              (* [comment removed for export] *)
  tp_a1 : getr R 11 = Z_to_bv 64 (hdr_cfglen content);                   (* [comment removed for export] *)
  tp_a2 : getr R 12 = Z_to_bv 64 (gm + 38 + hdr_cfglen content);         (* [comment removed for export] *)
  tp_a3 : getr R 13 = Z_to_bv 64 (hdr_paylen content);                   (* [comment removed for export] *)
  tp_s0 : getr R 8 = Z_to_bv 64 (gm + 34);
  tp_s1 : getr R 9 = Z_to_bv 64 (gm + 32);                               (* [comment removed for export] *)
  tp_s2 : getr R 18 = Z_to_bv 64 (hdr_cfglen content);
  tp_s3 : getr R 19 = Z_to_bv 64 (gm + 38 + hdr_cfglen content);
  tp_s4 : getr R 20 = Z_to_bv 64 (hdr_paylen content);
  tp_s5 : getr R 21 = Z_to_bv 64 (if hdr_b1 content <? 128 then hdr_b1 content else hdr_b1 content - 256 + 2 ^ 64);
            (* [comment removed for export] *)
  tp_s6 : getr R 22 = Z_to_bv 64 (gm + 32);
  (* [comment removed for export] *)
  tp_sp0 : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0;
  tp_len : 6 + hdr_cfglen content <= Z.of_nat (length content) < 65536;
  (* [comment removed for export] *)
  tp_stack : stack_writableZ M sp0;
  tp_frame : main_frame sp0 M;
  tp_world : world0 area gm brkv mas tid M;
  tp_content : rdn RSEGS M (Z_to_bv 64 (gm + 32)) (length content) = Some content
}.

(* [comment removed for export] *)
Definition iv_disjoint (p q : word * word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_target_pre ()) "(<.(2.(3.(=.&40.(>.(?.&40.)(?.&40.)O2.))(=.&40.(10.(?.&40.)(?.&40.)O2.)))(=.&40.(>.(?.&40.)(?.&40.)O1.)))(2.(3.(=.&40.(>.(?.&40.)(?.&40.)O1.))(=.&40.(10.(?.&40.)(?.&40.)O1.)))(=.&40.(>.(?.&40.)(?.&40.)O2.))))")
(* [comment removed for export] *).

Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (iv_disjoint p) l -> seps l -> seps (p :: l).

(* [comment removed for export] *)
Record target_vm (gm area : Z) (VM : VmMaps) : Prop := TARGET_VM {
  tv_res   : vm_reserved VM = segments_reserved RSEGS;
  tv_has   : In (Z_to_bv 64 gm, Z_to_bv 64 69632) (vm_maps VM);
  tv_area  : exists lo sz, In (lo, sz) (vm_maps VM)
               /\ bv_unsigned lo <= area /\ area + 4096 <= bv_unsigned lo + bv_unsigned sz;
  tv_len   : (length (vm_maps VM) <= 4)%nat;
  tv_small : Forall (fun p => 0 < bv_unsigned (snd p) <= 69632
                              /\ bv_unsigned (fst p) + bv_unsigned (snd p) <= 2 ^ 64) (vm_maps VM);
  tv_seps  : seps (vm_maps VM);
  tv_limit : vm_limit VM = source_alloc_limit
}.

(* [comment removed for export] *)
Definition t_target (content : list byte) (fs : Fs.Fs) : TSet :=
  let b2 := bv_unsigned (nth 2 content (Z_to_bv 8 0)) in
  let cfg := hdr_cfg content in
  let config_len := Z.to_nat (cfg mod 32768) in
  let counting := (32768 <=? cfg) in
  let payload_len := (length content - 6 - config_len)%nat in
  let calls := match config_len with O => 1%nat | _ => S (Z.to_nat (b2 mod 4)) end in
  let succ := t_emit (W 1 (zero_lines calls)) (t_exit (exit_code 0) fs) in
  match payload_len with
  | O => succ
  | _ => t_alt2 (t_exit (exit_code (if counting then 0 else 2)) fs) succ
  end.

