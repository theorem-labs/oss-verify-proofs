(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10-30: pool 14 row img-instcells-A (REPLY-IMG-ROWS.md (sha256 a33a582e3ffd; internal record); CF-UNIT-HYPS.md (sha256 77b3f94c95d2; internal record) line 50).
   Proves no function (kind: statement text; an IMAGE fact, a lookup in the unit's const-cell table).
   The cf layer's INST_CELLS_t (cgif YGcfInstSec.v:336-345 @ b81e8b96881, the instance object's constant cells that
   AGif2.sview reads) at fuzz_reply image A, over the unit's TfibSyms tables (lib/A/AF0m.v: TFIB_INST = 0xa2a58,
   Tfib_const). The reply tree does not carry YGcfInstSec.v yet, so inst_cells_A states INST_CELLS_t's text UNFOLDED at
   reply's image class instance AImg_reply (A/AGif2reply.v:23: im_segs := tfibsegs), over the symbol facts TfibSyms B;
   a consumer closes INST_CELLS_t B with (inst_cells_A B TS). Name and form match the B twin (a Theorem Labs lane, a Theorem Labs lane 05:02Z).
   Proof pattern: cgif's AGif5.view_AR (AGif5.v:248-257), tfib_const_lookup / tfib_const_lookup_sym over the const
   cells, here from the Forall over as_const B ly that INST_CELLS_t takes as its premise (no ARm needed). The table
   rows are found by vm_compute over Tfib_const, never typed: o_space and o_sec_chunks / +80 are symbolic rows
   (AInst _ -> ASp 0 / AQ 0); +0xe20, +0xe28, o_sec and +88 are numeric rows; the three bytes at o_sec_mutex + 1 are the
   rows z1 (+681) and z2 (+682). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AGif2reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* Three zero bytes from a zero byte and two zero bytes after it. *)
Lemma val_mem_zero_1_2 : forall (m : word -> option byte) a,
val_mem tfibsegs m a 1 0 -> val_mem tfibsegs m (a + 1) 2 0 -> val_mem tfibsegs m a 3 0.
Proof.
intros m a H1 H2 k Hk.
destruct k as [|[|[|k]]]; [| | |lia].
- exact (H1 0%nat ltac:(lia)).
- pose proof (H2 0%nat ltac:(lia)) as X. replace (a + Z.of_nat 1) with (a + 1 + Z.of_nat 0) by lia.
  replace (le_byte 0 3 1) with (le_byte 0 2 0) by reflexivity. exact X.
- pose proof (H2 1%nat ltac:(lia)) as X. replace (a + Z.of_nat 2) with (a + 1 + Z.of_nat 1) by lia.
  replace (le_byte 0 3 2) with (le_byte 0 2 1) by reflexivity. exact X.
Qed.

(* INST_CELLS_t B at reply A (UNFOLDED, at AImg_reply). *)
Theorem inst_cells_A : forall (B : asyms), TfibSyms B ->
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
intros B TS ly H mem _ _ C. change (@im_segs AImg_reply) with tfibsegs in *.
pose proof (ts_inst B TS) as EI.
assert (IN : forall c, In c (Tfib_const ly) -> cell_holds B ly (aview tfibsegs H mem) c)
by (intros c Hc; apply (proj1 (Forall_forall _ _) C); rewrite (ts_const B TS ly); exact Hc).
assert (CL : forall a w x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) ->
  val_mem tfibsegs (mrestrict H mem) a w x)
by (intros a w x E; exact (AF0x.cell_holds_val_mem B ly H mem (ANum a) w (ANum x) (IN _ (AF0x.cell_lookup_In _ _ _ E)))).
assert (CY : forall e w e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
  val_mem tfibsegs (mrestrict H mem) (aeval B ly e) w (aeval B ly e'))
by (intros e w e' E; exact (AF0x.cell_holds_val_mem B ly H mem e w e' (IN _ (AF0x.cell_lookup_In _ _ _ E)))).
rewrite EI.
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
- replace (TFIB_INST + o_space) with (aeval B ly (AInst o_space)) by (cbn; rewrite EI; reflexivity).
  replace (ly_space ly) with (aeval B ly (ASp 0)) by (cbn; lia). apply CY. vm_compute. reflexivity.
- apply CL. vm_compute. reflexivity.
- apply CL. vm_compute. reflexivity.
- apply CL. vm_compute. reflexivity.
- replace (TFIB_INST + o_sec_chunks) with (aeval B ly (AInst o_sec_chunks)) by (cbn; rewrite EI; reflexivity).
  replace (ly_Q ly) with (aeval B ly (AQ 0)) by (cbn; lia). apply CY. vm_compute. reflexivity.
- replace (TFIB_INST + 80) with (aeval B ly (AInst 80)) by (cbn; rewrite EI; reflexivity).
  replace (ly_Q ly) with (aeval B ly (AQ 0)) by (cbn; lia). apply CY. vm_compute. reflexivity.
- apply CL. vm_compute. reflexivity.
- apply val_mem_zero_1_2; apply CL; vm_compute; reflexivity.
Qed.

End R.
