(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/plugin-hostd/fuzz_reply/lib/A/ReplyImg_instcells.v (commit eb934de95d13, blob 9fcf1132663e) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 bff8519bbe3e; pin 1be0f53d96cb), from reply A d751b179ea49 (pin 42c58610e125); module paths changed; 0 image numerals moved by port_addr_check 3d2eee813cce MAPS predictions and the twins' symbol + offset map (0 model labels and sizes kept); no other numeral changed; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AF0l AF0m AF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Local Open Scope Z_scope.

Section R. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

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
intros B TS ly H mem _ _ C. change (@im_segs AImg_A) with tfibsegs in *.
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
