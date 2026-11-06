(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Frame Step Tac Image ZBridge SysStep SFModel ITree Nodes NodesM Decode DecodeM Arr.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import Prelim STree Malloc MallocCtrl KInv.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog MSafe KLink KStep KOwn KInit A_MallocBlocks A_MallocHINV A_MallocFacts_A A_Malloc_iface ImageChunks.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ref Require Import F_syscalls RMallocRep RMallocTree RMallocKit_B RMalloc_iface RMalloc_ifaceP RF_aligned16 RMalloc_init.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import StateGlue KRel KRelInit Room HeapCore MF AW MemFX.

Set Keyed Unification.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition AST_LO : Z := RMLOCK.
Definition AST_HI : Z := RCTX + 936.

Lemma rw_cells_image_rb : forall (m : word -> option byte) A bs,
  (forall a, A <= a < A + Z.of_nat (length bs) -> St.rb rsegs m a = St.img_byte rsegs a) ->
  rw_bytes_b rsegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
  rw_cells rsegs m A [CB (length bs) bs].
Proof.
  intros m A bs RB Hb HA Hl.
  pose proof (rw_bytes_b_sound rsegs bs A (fun _ => None) Hb (fun _ _ => eq_refl) HA Hl) as G.
  assert (G' : forall i b, nth_error bs i = Some b ->
            mrd rsegs m (wa (A + Z.of_nat i)) = Some b /\ wview rsegs m (wa (A + Z.of_nat i)) <> None).
  { intros i b Hi. pose proof (nth_error_Some_length' _ _ _ Hi) as L || assert (L : (i < length bs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    destruct (G i b Hi) as [R W]. split.
    - rewrite <- MemFX.rb_mrd, (RB (A + Z.of_nat i)) by lia. unfold St.img_byte, St.rom_of. unfold mrd, seg_rom in R. exact R.
    - unfold wview in W |- *. destruct (m (wa (A + Z.of_nat i))); [discriminate| exact W]. }
  split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [lia|].
    intros i Hi. destruct (nth_error bs i) as [b|] eqn:E; [apply (proj1 (G' i b E))|]. apply nth_error_None in E. lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [apply (proj2 (G' _ b E))|]. apply nth_error_None in E. lia.
Qed.

Ltac rimg_chunk_rb RB m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image_rb m A bs);
      [ intros a Ha; apply RB; cbn [length] in Ha; unfold AST_LO, AST_HI, RMLOCK, RCTX; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Lemma RHEAP_core_init : forall m : mem,
  (forall a, AST_LO <= a < AST_HI -> St.rb rsegs m a = St.img_byte rsegs a) ->
  RHEAP_core s0 [] m /\ rw_cells rsegs m RMREPL [C4 (wz 0)].
Proof.
  intros m RB.
  set (st0 := minit ctx_secret ref_reserved).
  rimg_chunk_rb RB m 0x87798%Z (ctx_head_cells st0) CXH.
  rimg_chunk_rb RB m (0x87798 + 80)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXA.
  rimg_chunk_rb RB m (0x87798 + 464)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXU.
  rimg_chunk_rb RB m (0x87798 + 848)%Z [CB 32 (zeros 32)] CXS.
  rimg_chunk_rb RB m (0x87798 + 880)%Z [CB 32 (zeros 32)] CXB.
  rimg_chunk_rb RB m (0x87798 + 912)%Z (ctx_tail_cells st0) CXT.
  rimg_chunk_rb RB m 0x87790%Z [C4 (wz 0)] ML.
  rimg_chunk_rb RB m 0x87b38%Z [C4 (wz 0)] MR.
  split; [| exact MR].
  exists st0, []. split; [apply Permutation_refl|]. split; [unfold s0, ps_init; cbn [ps_m]; rewrite reservedZ_ref; reflexivity|].
  split.
  2:{ unfold s0, ps_init; cbn [ps_brk]. apply HINV_from_init. }
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
  - unfold RMLOCK. exact ML.
  - intros a ar H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros b gh H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros rid r H. cbn in H. rewrite lookup_empty in H. discriminate.
Qed.

Lemma ceil_clamp_ok : forall sp : word, valid_sp sp ->
  let c := Z.max CEIL_MIN (Z.min CEIL_MAX ((bv_unsigned sp - 8388608) / 4096 * 4096)) in
  c <= bv_unsigned sp - 8388608 < c + 4096.
Proof.
  intros sp (Hlo & Hhi & _). unfold sp_window_lo, sp_window_hi, CEIL_MIN, CEIL_MAX in *. cbn zeta.
  pose proof (Z.mul_div_le (bv_unsigned sp - 8388608) 4096 ltac:(lia)) as H1.
  pose proof (Z_div_mod_eq_full (bv_unsigned sp - 8388608) 4096) as H2.
  pose proof (Z.mod_pos_bound (bv_unsigned sp - 8388608) 4096 ltac:(lia)) as H3.
  assert (34359207936 <= (bv_unsigned sp - 8388608) / 4096) by (apply Z.div_le_lower_bound; lia).
  assert ((bv_unsigned sp - 8388608) / 4096 <= 34359738368 - 2048) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Theorem aw_init : forall (m : mem) brk0 mbase sp lim inp tid,
  valid_brk rsegs brk0 ->
  alloc_ceiling <= bv_unsigned sp - 8388608 < alloc_ceiling + 4096 ->
  2 ^ 31 <= lim ->
  (forall a, AST_LO <= a < AST_HI -> St.rb rsegs m a = St.img_byte rsegs a) ->
  forall ws, NG ws -> aw_holds rsegs IMGX AWI (Z_to_bv 64 0) [] ws m (with_tid tid (init_model (segments_reserved rsegs) brk0 mbase sp lim inp)).
Proof.
  intros m brk0 mbase sp lim inp tid Hbrk Hceil Hlim RB ws NGW. apply aw_holdsW_intro; [| exact NGW].
  set (mo0 := init_model (segments_reserved rsegs) brk0 mbase sp lim inp).
  assert (VM : m_vmmaps (with_tid tid mo0) = mkVmMapsFull (segments_reserved rsegs) [] [] brk0 brk0 lim mbase sp) by reflexivity.
  destruct (RHEAP_core_init m RB) as [RC MR].
  exists s0, []. split; [apply Permutation_refl|]. split; [exact RC|]. split; [| split; [| split; [| exact MR]]].
  - apply (KREL_frame s0 [] mo0); [reflexivity| reflexivity|].
    unfold s0. apply KREL_init_ref; [exact Hbrk|].
    unfold ceil_ok, alloc_top.
    replace (vm_init_sp (m_vmmaps (init_model (segments_reserved rsegs) brk0 mbase sp lim inp))) with sp by reflexivity.
    unfold stack_max_size. lia.
  - reflexivity.
  - intros _. rewrite Z_to_bv_unsigned. cbn. split; [| left; auto].
    apply (room_init _ brk0 lim mbase sp VM Hlim).
Qed.

End CEIL.

From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Ubsan.
Module TwinB.
Import stdpp.base stdpp.decidable stdpp.list stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Image OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.NodesM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.DecodeM OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Arr.
Import OSSVerify.msgpack_c.unpack_pack_fuzzer.images.Ubsan.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Prelim OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Malloc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.MallocCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.KInv.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Monad OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.Prog OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.MSafe OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KLink OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KOwn OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.KInit OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocBlocks OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocHINV OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_MallocFacts_A OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.A_Malloc_iface OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ.ImageChunks.
Import F_syscalls.TwinB RMallocRep.TwinB RMallocTree.TwinB RMallocKit_B.TwinB RMalloc_iface.TwinB RMalloc_ifaceP.TwinB RF_aligned16.TwinB RMalloc_init.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.StateGlue OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.KRel OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.Room OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MemFX.
Import KRelInit.TwinB HeapCore.TwinB MF.TwinB AW.TwinB.

Set Keyed Unification.
Import ListNotations.
Import HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.CeilLia.
Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Definition AST_LO : Z := RMLOCK.
Definition AST_HI : Z := RCTX + 936.

Lemma rw_cells_image_rb : forall (m : word -> option byte) A bs,
  (forall a, A <= a < A + Z.of_nat (length bs) -> St.rb rsegs m a = St.img_byte rsegs a) ->
  rw_bytes_b rsegs A bs = true -> 0 <= A -> A + Z.of_nat (length bs) <= 2^64 ->
  rw_cells rsegs m A [CB (length bs) bs].
Proof.
  intros m A bs RB Hb HA Hl.
  pose proof (rw_bytes_b_sound rsegs bs A (fun _ => None) Hb (fun _ _ => eq_refl) HA Hl) as G.
  assert (G' : forall i b, nth_error bs i = Some b ->
            mrd rsegs m (wa (A + Z.of_nat i)) = Some b /\ wview rsegs m (wa (A + Z.of_nat i)) <> None).
  { intros i b Hi. pose proof (nth_error_Some_length' _ _ _ Hi) as L || assert (L : (i < length bs)%nat) by (apply nth_error_Some; rewrite Hi; discriminate).
    destruct (G i b Hi) as [R W]. split.
    - rewrite <- MemFX.rb_mrd, (RB (A + Z.of_nat i)) by lia. unfold St.img_byte, St.rom_of. unfold mrd, seg_rom in R. exact R.
    - unfold wview in W |- *. destruct (m (wa (A + Z.of_nat i))); [discriminate| exact W]. }
  split; [split|].
  - cbn. split; [reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. split; [lia|]. split; [lia|].
    intros i Hi. destruct (nth_error bs i) as [b|] eqn:E; [apply (proj1 (G' i b E))|]. apply nth_error_None in E. lia.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. split; [lia|]. split; [lia|].
    intros i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:E; [apply (proj2 (G' _ b E))|]. apply nth_error_None in E. lia.
Qed.

Ltac rimg_chunk_rb RB m A cs H :=
  let bs := eval vm_compute in (cells_bytes cs) in
  assert (H : rw_cells rsegs m A cs);
  [ apply (rw_cells_recast rsegs m A [CB (length bs) bs] cs);
    [ apply (rw_cells_image_rb m A bs);
      [ intros a Ha; apply RB; cbn [length] in Ha; unfold AST_LO, AST_HI, RMLOCK, RCTX; lia | vm_compute; reflexivity | lia | cbn [length]; lia ]
    | cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity ]
  | ].

Lemma RHEAP_core_init : forall m : mem,
  (forall a, AST_LO <= a < AST_HI -> St.rb rsegs m a = St.img_byte rsegs a) ->
  RHEAP_core s0 [] m /\ rw_cells rsegs m RMREPL [C4 (wz 0)].
Proof.
  intros m RB.
  set (st0 := minit ctx_secret ref_reserved).
  rimg_chunk_rb RB m 0x88f98%Z (ctx_head_cells st0) CXH.
  rimg_chunk_rb RB m (0x88f98 + 80)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXA.
  rimg_chunk_rb RB m (0x88f98 + 464)%Z [CB 384 (u64s (repeat (wz 0) 48))] CXU.
  rimg_chunk_rb RB m (0x88f98 + 848)%Z [CB 32 (zeros 32)] CXS.
  rimg_chunk_rb RB m (0x88f98 + 880)%Z [CB 32 (zeros 32)] CXB.
  rimg_chunk_rb RB m (0x88f98 + 912)%Z (ctx_tail_cells st0) CXT.
  rimg_chunk_rb RB m 0x88f90%Z [C4 (wz 0)] ML.
  rimg_chunk_rb RB m 0x89338%Z [C4 (wz 0)] MR.
  split; [| exact MR].
  exists st0, []. split; [apply Permutation_refl|]. split; [unfold s0, ps_init; cbn [ps_m]; rewrite reservedZ_ref; reflexivity|].
  split.
  2:{ unfold s0, ps_init; cbn [ps_brk]. apply HINV_from_init. }
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
  - unfold RMLOCK. exact ML.
  - intros a ar H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros b gh H. cbn in H. rewrite lookup_empty in H. discriminate.
  - intros rid r H. cbn in H. rewrite lookup_empty in H. discriminate.
Qed.

Lemma ceil_clamp_ok : forall sp : word, valid_sp sp ->
  let c := Z.max CEIL_MIN (Z.min CEIL_MAX ((bv_unsigned sp - 8388608) / 4096 * 4096)) in
  c <= bv_unsigned sp - 8388608 < c + 4096.
Proof.
  intros sp (Hlo & Hhi & _). unfold sp_window_lo, sp_window_hi, CEIL_MIN, CEIL_MAX in *. cbn zeta.
  pose proof (Z.mul_div_le (bv_unsigned sp - 8388608) 4096 ltac:(lia)) as H1.
  pose proof (Z_div_mod_eq_full (bv_unsigned sp - 8388608) 4096) as H2.
  pose proof (Z.mod_pos_bound (bv_unsigned sp - 8388608) 4096 ltac:(lia)) as H3.
  assert (34359207936 <= (bv_unsigned sp - 8388608) / 4096) by (apply Z.div_le_lower_bound; lia).
  assert ((bv_unsigned sp - 8388608) / 4096 <= 34359738368 - 2048) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

Theorem aw_init : forall (m : mem) brk0 mbase sp lim inp tid,
  valid_brk rsegs brk0 ->
  alloc_ceiling <= bv_unsigned sp - 8388608 < alloc_ceiling + 4096 ->
  2 ^ 31 <= lim ->
  (forall a, AST_LO <= a < AST_HI -> St.rb rsegs m a = St.img_byte rsegs a) ->
  forall ws, NG ws -> aw_holds rsegs IMGX AWI (Z_to_bv 64 0) [] ws m (with_tid tid (init_model (segments_reserved rsegs) brk0 mbase sp lim inp)).
Proof.
  intros m brk0 mbase sp lim inp tid Hbrk Hceil Hlim RB ws NGW. apply aw_holdsW_intro; [| exact NGW].
  set (mo0 := init_model (segments_reserved rsegs) brk0 mbase sp lim inp).
  assert (VM : m_vmmaps (with_tid tid mo0) = mkVmMapsFull (segments_reserved rsegs) [] [] brk0 brk0 lim mbase sp) by reflexivity.
  destruct (RHEAP_core_init m RB) as [RC MR].
  exists s0, []. split; [apply Permutation_refl|]. split; [exact RC|]. split; [| split; [| split; [| exact MR]]].
  - apply (KREL_frame s0 [] mo0); [reflexivity| reflexivity|].
    unfold s0. apply KREL_init_ref; [exact Hbrk|].
    unfold ceil_ok, alloc_top.
    replace (vm_init_sp (m_vmmaps (init_model (segments_reserved rsegs) brk0 mbase sp lim inp))) with sp by reflexivity.
    unfold stack_max_size. lia.
  - reflexivity.
  - intros _. rewrite Z_to_bv_unsigned. cbn. split; [| left; auto].
    apply (room_init _ brk0 lim mbase sp VM Hlim).
Qed.

End CEIL.
End TwinB.
