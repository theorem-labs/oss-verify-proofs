(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_malloc_free A_MallocHINV A_MallocFacts_A A_Malloc_iface ImageChunks.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMalloc_iface.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma u64arr_of_rw_cells' : forall m A n bs k, rw_cells rsegs m A [CB n bs] -> bs = u64s (repeat (wz 0) k) -> (n = 8 * k)%nat ->
  u64arr rsegs m A (repeat (wz 0) k).
Proof.
  intros m A n bs k [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  split; [exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. exact HW.
Qed.

Ltac rimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Lemma RHEAP_init_proof : forall (m : mem) (auxv : word) (ctd thr sec : byte) (tm1 tlsh tlss tlsa tlsc : word) (gl : list byte),
  (forall a : word, 0x87790 <= bv_unsigned a < 0x87b38 -> m a = None) ->
  rw_cells rsegs m 0x87720 [C1 ctd; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  rw_cells rsegs m 0x87728 [C8 auxv; C8 tlsh; C8 tlss; C8 tlsa; C8 tlsc; C8 (Z_to_bv 64 4096); CB 48 gl] ->
  rw_cells rsegs m 0x55660 [C8 (Z_to_bv 64 0x87700)] ->
  rw_cells rsegs m 0x87700 [C8 (wz ssp_canary)] ->
  mem_inv rsegs m ->
  RHEAP (ps_init (reservedZ rsegs)) [] m
  /\ rw_cells rsegs m RAUXV_CELL [C8 auxv].
Proof.
  intros m auxv ctd thr sec tm1 tlsh tlss tlsa tlsc gl NONE LC LC2 GOT GUARD MI.
  set (st0 := minit ctx_secret ref_reserved).
  rimg_chunk NONE m 0x87798%Z (ctx_head_cells st0) CXH.
  rimg_chunk NONE m (0x87798 + 80)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXA.
  rimg_chunk NONE m (0x87798 + 464)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXU.
  rimg_chunk NONE m (0x87798 + 848)%Z [CB 32 (zeros 32)] CXS.
  rimg_chunk NONE m (0x87798 + 880)%Z [CB 32 (zeros 32)] CXB.
  rimg_chunk NONE m (0x87798 + 912)%Z (ctx_tail_cells st0) CXT.
  rimg_chunk NONE m 0x87790%Z [C4 (wz 0)] ML.

  pose proof (proj1 (rw_cells_app rsegs m 0x87720 [C1 ctd; C1 thr; C1 sec] _) LC) as [_ LC3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LC3.
  pose proof (proj1 (rw_cells_app rsegs m (0x87720 + 3) [C1 (Z_to_bv 8 0)] _) LC3) as [NL _].
  pose proof (proj1 (rw_cells_app rsegs m 0x87728 [C8 auxv] _) LC2) as [AUXC LC16]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LC16.
  pose proof (proj1 (rw_cells_app rsegs m (0x87728 + 8) [C8 tlsh; C8 tlss; C8 tlsa; C8 tlsc] _) LC16) as [_ LC48].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in LC48.
  pose proof (proj1 (rw_cells_app rsegs m _ [C8 (Z_to_bv 64 4096)] _) LC48) as [PS _].
  split.
  2:{ unfold RAUXV_CELL. exact AUXC. }
  exists st0, []. split; [apply Permutation_refl|]. split; [unfold ps_init; cbn [ps_m]; rewrite reservedZ_ref; reflexivity|].
  split.
  2:{ unfold ps_init; cbn [ps_brk]. apply HINV_from_init. }
  split; [|split; [|split; [|split; [|split]]]].
  -   split; [reflexivity|]. split; [intros rid r H; rewrite lookup_empty in H; discriminate|].
    split; [intros ? ? ? ? H; rewrite lookup_empty in H; discriminate|].
    split; [intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate|].
    intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate.
  - unfold rmrep_ctx, RCTX. split; [exact CXH|]. split; [|split; [|split; [|split]]].
    + replace (actives st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXA| reflexivity| reflexivity].
    + replace (usages st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXU| reflexivity| reflexivity].
    + replace (unmap_seqs st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32). exact CXS.
    + replace (bouncess st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32). exact CXB.
    + exact CXT.
  - unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD. split; [exact ML|]. split; [|split; [|split]].
    + match goal with |- rw_cells _ _ ?G _ => match type of NL with rw_cells _ _ ?A _ => replace G with A by reflexivity end end.
      change (b8 0) with (Z_to_bv 8 0). exact NL.
    + match goal with |- rw_cells _ _ ?G _ => match type of PS with rw_cells _ _ ?A _ => replace G with A by reflexivity end end.
      change (wz 4096) with (Z_to_bv 64 4096). exact PS.
    + change (wz 554752) with (Z_to_bv 64 0x87700). exact GOT.
    + exact GUARD.
  - intros a ar H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros b gh H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros rid r H. cbn in H. rewrite lookup_empty in H. discriminate.
Qed.

End CEIL.

Ltac rimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_F_malloc_free OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.ImageChunks.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog.
Import RMallocRep.TwinB RMallocTree.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB.

Set Keyed Unification.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma u64arr_of_rw_cells' : forall m A n bs k, rw_cells rsegs m A [CB n bs] -> bs = u64s (repeat (wz 0) k) -> (n = 8 * k)%nat ->
  u64arr rsegs m A (repeat (wz 0) k).
Proof.
  intros m A n bs k [[Hwf HB] HW] -> Hn. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  split; [exact HB|]. cbn [cells_size csize] in HW. rewrite repeat_length. replace (8 * Z.of_nat k) with (Z.of_nat (n + 0)) by lia. exact HW.
Qed.

Ltac rimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Lemma RHEAP_init_proof : forall (m : mem) (auxv : word) (ctd thr sec : byte) (tm1 tlsh tlss tlsa tlsc : word) (gl : list byte),
  (forall a : word, 0x88f90 <= bv_unsigned a < 0x89338 -> m a = None) ->
  rw_cells rsegs m 0x88f20 [C1 ctd; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->
  rw_cells rsegs m 0x88f28 [C8 auxv; C8 tlsh; C8 tlss; C8 tlsa; C8 tlsc; C8 (Z_to_bv 64 4096); CB 48 gl] ->
  rw_cells rsegs m 0x56e68 [C8 (Z_to_bv 64 0x88f00)] ->
  rw_cells rsegs m 0x88f00 [C8 (wz ssp_canary)] ->
  mem_inv rsegs m ->
  RHEAP (ps_init (reservedZ rsegs)) [] m
  /\ rw_cells rsegs m RAUXV_CELL [C8 auxv].
Proof.
  intros m auxv ctd thr sec tm1 tlsh tlss tlsa tlsc gl NONE LC LC2 GOT GUARD MI.
  set (st0 := minit ctx_secret ref_reserved).
  rimg_chunk NONE m 0x88f98%Z (ctx_head_cells st0) CXH.
  rimg_chunk NONE m (0x88f98 + 80)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXA.
  rimg_chunk NONE m (0x88f98 + 464)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXU.
  rimg_chunk NONE m (0x88f98 + 848)%Z [CB 32 (zeros 32)] CXS.
  rimg_chunk NONE m (0x88f98 + 880)%Z [CB 32 (zeros 32)] CXB.
  rimg_chunk NONE m (0x88f98 + 912)%Z (ctx_tail_cells st0) CXT.
  rimg_chunk NONE m 0x88f90%Z [C4 (wz 0)] ML.

  pose proof (proj1 (rw_cells_app rsegs m 0x88f20 [C1 ctd; C1 thr; C1 sec] _) LC) as [_ LC3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LC3.
  pose proof (proj1 (rw_cells_app rsegs m (0x88f20 + 3) [C1 (Z_to_bv 8 0)] _) LC3) as [NL _].
  pose proof (proj1 (rw_cells_app rsegs m 0x88f28 [C8 auxv] _) LC2) as [AUXC LC16]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in LC16.
  pose proof (proj1 (rw_cells_app rsegs m (0x88f28 + 8) [C8 tlsh; C8 tlss; C8 tlsa; C8 tlsc] _) LC16) as [_ LC48].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in LC48.
  pose proof (proj1 (rw_cells_app rsegs m _ [C8 (Z_to_bv 64 4096)] _) LC48) as [PS _].
  split.
  2:{ unfold RAUXV_CELL. exact AUXC. }
  exists st0, []. split; [apply Permutation_refl|]. split; [unfold ps_init; cbn [ps_m]; rewrite reservedZ_ref; reflexivity|].
  split.
  2:{ unfold ps_init; cbn [ps_brk]. apply HINV_from_init. }
  split; [|split; [|split; [|split; [|split]]]].
  -   split; [reflexivity|]. split; [intros rid r H; rewrite lookup_empty in H; discriminate|].
    split; [intros ? ? ? ? H; rewrite lookup_empty in H; discriminate|].
    split; [intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate|].
    intros ? ? H; cbn in H; rewrite lookup_empty in H; discriminate.
  - unfold rmrep_ctx, RCTX. split; [exact CXH|]. split; [|split; [|split; [|split]]].
    + replace (actives st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXA| reflexivity| reflexivity].
    + replace (usages st0) with (repeat (wz 0) 48) by reflexivity. eapply u64arr_of_rw_cells'; [exact CXU| reflexivity| reflexivity].
    + replace (unmap_seqs st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32). exact CXS.
    + replace (bouncess st0) with (zeros 32) by reflexivity. apply (u8arr_of_rw_cells rsegs m _ 32). exact CXB.
    + exact CXT.
  - unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RGOT_SSP, RSSP_GUARD. split; [exact ML|]. split; [|split; [|split]].
    + match goal with |- rw_cells _ _ ?G _ => match type of NL with rw_cells _ _ ?A _ => replace G with A by reflexivity end end.
      change (b8 0) with (Z_to_bv 8 0). exact NL.
    + match goal with |- rw_cells _ _ ?G _ => match type of PS with rw_cells _ _ ?A _ => replace G with A by reflexivity end end.
      change (wz 4096) with (Z_to_bv 64 4096). exact PS.
    + change (wz 560896) with (Z_to_bv 64 0x88f00). exact GOT.
    + exact GUARD.
  - intros a ar H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros b gh H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros rid r H. cbn in H. rewrite lookup_empty in H. discriminate.
Qed.

End CEIL.

Ltac rimg_chunk NONE m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image0 rsegs m A bs);
      [ intros a Ha; apply NONE; cbn [length] in Ha; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].
End TwinB.
