(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/ReplyImg_instcells.v (commit 4d286b2e618d, file sha256 b701b5915388) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 0 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal by the same symbol map), and 0 addresses named in comments; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10-30 (a prior worker): the body of INST_CELLS_t from
   proofs/cgif/cgif_file_fuzzer/lib/YGcfInstSec.v (commit b81e8b96881) stated unfolded at fuzz_reply image B's names, and
   proved by the cell lookup pattern of lib/B/AGif2.v (cell_holds_val_mem over as_const) against reply B's Tfib_const. *)
(* Theorem Labs, 2026-10-30 (a prior worker; plugin-hostd/fuzz_reply, image B).
   rule 24: no function proved (kind: image fact, a const-cell table lookup at plugin-hostd/fuzz_reply image B).

   inst_cells_B is the cgif-layer image fact INST_CELLS_t of proofs/cgif/cgif_file_fuzzer/lib/YGcfInstSec.v
   (lines 336-345 at commit b81e8b96881) at reply B's symbol table.  The reply tree does not carry YGcfInstSec, so the
   body of INST_CELLS_t B is stated UNFOLDED, verbatim, at the reply's names: im_segs is AGif2cgif.AImg_reply's
   (= tfibsegs, lib/B/YB1v.v), and the symbol table is any B with TfibSyms B (lib/B/YF0m.v).

   Proof: under TfibSyms B, as_inst B = TFIB_INST (ts_inst) and as_const B ly = Tfib_const ly (ts_const).  Each cell is
   found in reply B's table Tfib_const by `cell_lookup` (ImgBase.v) and vm_compute, at the address and value the
   statement names, and is read out of the Forall hypothesis by cell_holds_val_mem (the pattern of lib/B/AGif2.v:77-90):
   - inst + o_space, inst + o_sec_chunks, inst + 80: the symbolic cells c8 (AInst _) (ASp 0) / (AQ 0) of Tfib_const_sym;
   - inst + 0xe20, inst + 0xe28, inst + o_sec, inst + 88: literal 8-byte cells of Tfib_const_abs;
   - inst + o_sec_mutex + 1 (3 bytes of 0): the 1-byte zero cell at inst + o_sec_mutex + 1 and the 2-byte zero cell at
     inst + o_sec_mutex + 2 of Tfib_const_abs, joined byte by byte. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* = YGcfInstSec.INST_CELLS_t B (YGcfInstSec.v:336-345 at b81e8b96881), unfolded, for every B with TfibSyms B. *)
Lemma inst_cells_B : forall (B : asyms), TfibSyms B ->
  forall ly (H : word -> bool) (mem : word -> option byte), layout_ok ly -> ly_tsd ly = as_tsd B ->
  Forall (cell_holds B ly (aview im_segs H mem)) (as_const B ly) ->
  val_mem im_segs (mrestrict H mem) (as_inst B + o_space) 8 (ly_space ly) /\
  val_mem im_segs (mrestrict H mem) (as_inst B + 0xe20) 8 0x10000000000 /\
  val_mem im_segs (mrestrict H mem) (as_inst B + 0xe28) 8 0x108000010 /\
  val_mem im_segs (mrestrict H mem) (as_inst B + o_sec) 8 4096 /\
  val_mem im_segs (mrestrict H mem) (as_inst B + o_sec_chunks) 8 (ly_Q ly) /\
  val_mem im_segs (mrestrict H mem) (as_inst B + 80) 8 (ly_Q ly) /\
  val_mem im_segs (mrestrict H mem) (as_inst B + 88) 8 kPtrArrayResv /\
  val_mem im_segs (mrestrict H mem) (as_inst B + o_sec_mutex + 1) 3 0.
Proof.
intros B TS ly H mem _ _ HC.
(* a cell that reply B's table holds is in memory (AGif2.sv_cell_sym / sv_cell_lit) *)
assert (CY : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
  val_mem im_segs (mrestrict H mem) (aeval B ly e) w (aeval B ly e')).
{ intros e w e' E. apply (cell_holds_val_mem im_segs B ly H mem e w e').
  apply (proj1 (Forall_forall (cell_holds B ly (aview im_segs H mem)) (as_const B ly)) HC).
  rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E). }
assert (CL : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) ->
  val_mem im_segs (mrestrict H mem) a w x).
{ intros a w x E. exact (CY (ANum a) w (ANum x) E). }
(* the symbolic cells of Tfib_const_sym *)
assert (L1 : cell_lookup (Tfib_const ly) (AInst o_space) = Some (ACell (AInst o_space) 8 (AV (ASp 0))))
  by (vm_compute; reflexivity).
assert (L5 : cell_lookup (Tfib_const ly) (AInst o_sec_chunks) = Some (ACell (AInst o_sec_chunks) 8 (AV (AQ 0))))
  by (vm_compute; reflexivity).
assert (L6 : cell_lookup (Tfib_const ly) (AInst 80) = Some (ACell (AInst 80) 8 (AV (AQ 0))))
  by (vm_compute; reflexivity).
pose proof (CY _ _ _ L1) as C1. pose proof (CY _ _ _ L5) as C5. pose proof (CY _ _ _ L6) as C6.
cbn [aeval] in C1, C5, C6. rewrite Z.add_0_r in C1, C5, C6.
pose proof (ts_inst B TS) as EI. rewrite EI in C1, C5, C6. rewrite EI.
(* the literal cells of Tfib_const_abs, at the addresses and values the statement names *)
assert (L2 : cell_lookup (Tfib_const ly) (ANum (TFIB_INST + 0xe20)) =
  Some (ACell (ANum (TFIB_INST + 0xe20)) 8 (AV (ANum 0x10000000000)))) by (vm_compute; reflexivity).
assert (L3 : cell_lookup (Tfib_const ly) (ANum (TFIB_INST + 0xe28)) =
  Some (ACell (ANum (TFIB_INST + 0xe28)) 8 (AV (ANum 0x108000010)))) by (vm_compute; reflexivity).
assert (L4 : cell_lookup (Tfib_const ly) (ANum (TFIB_INST + o_sec)) =
  Some (ACell (ANum (TFIB_INST + o_sec)) 8 (AV (ANum 4096)))) by (vm_compute; reflexivity).
assert (L7 : cell_lookup (Tfib_const ly) (ANum (TFIB_INST + 88)) =
  Some (ACell (ANum (TFIB_INST + 88)) 8 (AV (ANum kPtrArrayResv)))) by (vm_compute; reflexivity).
assert (LM1 : cell_lookup (Tfib_const ly) (ANum (TFIB_INST + o_sec_mutex + 1)) =
  Some (ACell (ANum (TFIB_INST + o_sec_mutex + 1)) 1 (AV (ANum 0)))) by (vm_compute; reflexivity).
assert (LM2 : cell_lookup (Tfib_const ly) (ANum (TFIB_INST + o_sec_mutex + 2)) =
  Some (ACell (ANum (TFIB_INST + o_sec_mutex + 2)) 2 (AV (ANum 0)))) by (vm_compute; reflexivity).
pose proof (CL _ _ _ L2) as C2. pose proof (CL _ _ _ L3) as C3. pose proof (CL _ _ _ L4) as C4.
pose proof (CL _ _ _ L7) as C7. pose proof (CL _ _ _ LM1) as M1. pose proof (CL _ _ _ LM2) as M2.
(* the 3 zero bytes at inst + o_sec_mutex + 1: the 1-byte cell, then the 2 bytes of the 2-byte cell *)
assert (C8 : val_mem im_segs (mrestrict H mem) (TFIB_INST + o_sec_mutex + 1) 3 0).
{ intros k Hk. destruct k as [|[|[|k]]]; [| | | lia].
  - rewrite (M1 0%nat ltac:(lia)). reflexivity.
  - replace (TFIB_INST + o_sec_mutex + 1 + Z.of_nat 1) with (TFIB_INST + o_sec_mutex + 2 + Z.of_nat 0) by lia.
    rewrite (M2 0%nat ltac:(lia)). reflexivity.
  - replace (TFIB_INST + o_sec_mutex + 1 + Z.of_nat 2) with (TFIB_INST + o_sec_mutex + 2 + Z.of_nat 1) by lia.
    rewrite (M2 1%nat ltac:(lia)). reflexivity. }
exact (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 (conj C6 (conj C7 C8))))))).
Qed.
End a.
