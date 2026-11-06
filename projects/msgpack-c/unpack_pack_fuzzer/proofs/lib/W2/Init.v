(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs MemProofs StepSoundBase GTwinSub.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Mem Frame.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step ValP MemP StepB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.

Module WInit.
Definition w0 : word := Z_to_bv 64 0.
Definition MOW : Model := mkModel [] (mkVmMapsFull [] [] [] w0 w0 0 w0 w0) IEof [] None None None.
Lemma MOW_facts : mfacts MOW. Proof. split; reflexivity. Qed.
Definition OPSW : optable := plain_optable (fun _ _ _ _ => True) (fun _ _ => []) (fun _ _ _ _ _ _ _ h => h).

Definition PRIVW : list (int * int) := [(864256%uint63, 6483968%uint63)].
Definition image_region : region := Region 0%uint63 (VL wzero) true BGImage IMap.empty.
Definition stack_region (ROOM : Z) : region := Region (Uint63.of_Z (- ROOM)) (VL wzero) true BGNone IMap.empty.
Definition regsW (ROOM : Z) : IMap.t region := IMap.add 1%uint63 (stack_region ROOM) (IMap.add 0%uint63 image_region IMap.empty).
Definition wstate (ROOM : Z) (pc : int) (xf ff : rf sv) (facts : list fact) (next : int) : sstate :=
  SS pc xf ff RNone (regsW ROOM) facts [] PRIVW next.

Section I.
Variable ROOM : Z.
Hypothesis ROOMR : 0 < ROOM < 2 ^ 40.

Lemma regsW_bst : IMap.bst (regsW ROOM).
Proof. unfold regsW. apply IMap.bst_add, IMap.bst_add, IMap.bst_empty. Qed.

Lemma regsW_find : forall k r, IMap.find k (regsW ROOM) = Some r ->
  (k = 1%uint63 /\ r = stack_region ROOM) \/ (k = 0%uint63 /\ r = image_region).
Proof.
  intros k r H. unfold regsW in H.
  destruct (PrimInt63.eqb 1%uint63 k) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst k. rewrite IMap.find_add_same in H by (apply IMap.bst_add, IMap.bst_empty). injection H as <-. left. auto.
  - rewrite IMap.find_add_other_eqb in H by (first [apply IMap.bst_add, IMap.bst_empty | exact K1]).
    destruct (PrimInt63.eqb 0%uint63 k) eqn:K0.
    + apply Uint63.eqb_correct in K0. subst k. rewrite IMap.find_add_same in H by apply IMap.bst_empty. injection H as <-. right. auto.
    + rewrite IMap.find_add_other_eqb in H by (first [apply IMap.bst_empty | exact K0]). rewrite IMap.find_empty in H. discriminate H.
Qed.

Lemma loZ_stack : loZ (stack_region ROOM) = - ROOM.
Proof. unfold loZ, stack_region. cbn [rg_lo]. apply GTwinSub.keyZ_of_Z. lia. Qed.
Lemma hiZ_stack : forall E, hiZ E (stack_region ROOM) = 0.
Proof. intros E. unfold hiZ, stack_region. cbn [rg_hi den]. reflexivity. Qed.

Lemma stack_region_ok : forall E (m : word -> option byte) lo,
  AF.stk asegs m lo (bv_unsigned (ev E 1%uint63)) -> lo <= bv_unsigned (ev E 1%uint63) - ROOM -> 0x62f000 <= lo ->
  region_ok asegs PRIVW E m 1%uint63 (stack_region ROOM).
Proof.
  intros E m lo (S0 & S1 & SV) LO IMG.
  pose proof (bv_unsigned_in_range 64 (ev E 1%uint63)) as RB. rewrite bv_modulus_64 in RB. unfold W64.two64 in RB.
  constructor.
  - exact (@IMap.bst_empty gran).
  - intros _. rewrite loZ_stack, hiZ_stack. unfold two64. lia.
  - intros _ a Ha. rewrite loZ_stack, hiZ_stack in Ha.
    destruct (SV a ltac:(lia)) as [WV (b & RD)].
    split; [| split].
    + change (rb asegs m a) with (AM.mrd asegs m (AM.wa a)). rewrite RD. discriminate.
    + intros _. unfold wb. fold (AM.wa a). destruct (wview asegs m (AM.wa a)); [reflexivity| contradiction].
    + apply ref_find_segment_none; lia.
  - intros g gr H. cbn [stack_region rg_cells] in H. rewrite IMap.find_empty in H. discriminate H.
  - intros g gr c i H. cbn [stack_region rg_cells] in H. rewrite IMap.find_empty in H. discriminate H.
  - intros o _ _ _. cbn [bg_byte stack_region rg_bg]. exact I.
Qed.

Lemma image_region_ok : forall E (m : word -> option byte),
  ev E 0%uint63 = Z_to_bv 64 0 -> AM.mem_inv asegs m ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (AM.wa i) = None) ->
  region_ok asegs PRIVW E m 0%uint63 image_region.
Proof.
  intros E m EZ MI RR. constructor.
  - exact (@IMap.bst_empty gran).
  - intros K; discriminate K.
  - intros K; discriminate K.
  - intros g gr H. cbn [image_region rg_cells] in H. rewrite IMap.find_empty in H. discriminate H.
  - intros g gr c i H. cbn [image_region rg_cells] in H. rewrite IMap.find_empty in H. discriminate H.
  - intros o _ H0 _. destruct (H0 eq_refl) as (OR & (bs & RD) & NP). cbn [bg_byte image_region rg_bg]. unfold img_byte.
    rewrite EZ. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_l.
    assert (O64 : 0 <= o < 2 ^ 64) by (unfold two63 in OR; lia).
    assert (UO : bv_unsigned (Z_to_bv 64 o) = o) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
    assert (INIMG : 0x10000 <= o < 0x62f000).
    { destruct (Z_lt_le_dec o 0x10000) as [L|L]; [| destruct (Z_lt_le_dec o 0x62f000) as [L2|L2]; [lia|]].
      - rewrite (ref_memory_read_none (Z_to_bv 64 o) 1 ltac:(cbn; lia) ltac:(rewrite UO; cbn; lia)) in RD. discriminate RD.
      - rewrite (ref_memory_read_none (Z_to_bv 64 o) 1 ltac:(cbn; lia) ltac:(rewrite UO; cbn; lia)) in RD. discriminate RD. }
    assert (NPR : o < 0xd3000).
    { destruct (Z_lt_le_dec o 0xd3000) as [L|L]; [exact L|]. exfalso. apply NP. unfold in_priv, PRIVW.
      apply Exists_cons_hd. cbn [fst snd]. change (to_Z 864256%uint63) with 864256. change (to_Z 6483968%uint63) with 6483968. lia. }
    assert (MN : m (Z_to_bv 64 o) = None).
    { destruct (Z_lt_le_dec o 0xcd000) as [L|L].
      - destruct (m (Z_to_bv 64 o)) as [b|] eqn:MB; [| reflexivity]. exfalso.
        pose proof (MI _ _ MB) as RO. rewrite a_ro_addr, UO in RO.
        destruct (Z.leb_spec0 0x10000 o); destruct (Z.ltb_spec0 o 0xcd000); cbn in RO; try discriminate RO; lia.
      - apply (RR o). unfold ARELRO_LO, ARELRO_HI. lia. }
    destruct (rom_of asegs (Z_to_bv 64 o)) as [b|] eqn:RM; [| exact I]. unfold rb. rewrite MN. exact RM.
Qed.

Theorem init_ok : forall E ms pc xf ff facts next lo,
  ms_pc_val ms = Z_to_bv 64 (to_Z pc) ->
  rf_get xf X0 = VL wzero ->
  (forall r, rget (core_of ms) (reg_of_r5 r) = den E (rf_get xf r)) ->
  (forall r, reg_get (ms_fregs ms) (reg_of_r5 r) = den E (rf_get ff r)) ->
  ms_svc_pending ms = None -> ms_resv ms = None -> bv_unsigned (ms_fcsr ms) < 32 -> ms_rom ms = rom_of asegs ->
  ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E facts ->
  AF.stk asegs (ms_mem ms) lo (bv_unsigned (ev E 1%uint63)) -> lo <= bv_unsigned (ev E 1%uint63) - ROOM -> 0x62f000 <= lo ->
  AM.mem_inv asegs (ms_mem ms) ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> ms_mem ms (AM.wa i) = None) ->
  st_ok asegs OPSW E (wstate ROOM pc xf ff facts next) ms MOW.
Proof.
  intros E ms pc xf ff facts next lo HPC HX0 HR HF SVC RSV FC ROM EZ FH STK LO IMG MI RR.
  constructor; cbn [wstate s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  - exact HPC.
  - exact HX0.
  - exact HR.
  - exact HF.
  - exact SVC.
  - cbn [resv_ok]. exact RSV.
  - exact FC.
  - exact ROM.
  - exact EZ.
  - exact regsW_bst.
  - intros k r H. destruct (regsW_find k r H) as [[-> ->]|[-> ->]].
    + exact (stack_region_ok E (ms_mem ms) lo STK LO IMG).
    + exact (image_region_ok E (ms_mem ms) EZ MI RR).
  - intros k1 r1 k2 r2 H1 H2 NE K1 K2 _ a _.
    destruct (regsW_find k1 r1 H1) as [[-> ->]|[-> ->]]; [| discriminate K1].
    destruct (regsW_find k2 r2 H2) as [[-> ->]|[-> ->]]; [apply NE; reflexivity| discriminate K2].
  - intros r g gr c H. destruct (regsW_find _ _ H) as [[X _]|[_ ->]]; [discriminate X|].
    intros HG. cbn [image_region rg_cells] in HG. rewrite IMap.find_empty in HG. discriminate HG.
  - exact FH.
  - unfold ops_hold. constructor.
  - unfold ops_apart. constructor.
  - exact MOW_facts.
  - intros a _. left. exact I.
  - intros a b MB seg FS. pose proof (MI _ _ MB) as RO. unfold AM.ro_addr in RO. rewrite FS in RO.
    destruct (seg_writable seg); [reflexivity| discriminate RO].
Qed.

End I.
End WInit.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.GTwinSub.
Import ABase.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step ValP MemP StepB.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module AM := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem.
Module AF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame.

Module WInit.
Definition w0 : word := Z_to_bv 64 0.
Definition MOW : Model := mkModel [] (mkVmMapsFull [] [] [] w0 w0 0 w0 w0) IEof [] None None None.
Lemma MOW_facts : mfacts MOW. Proof. split; reflexivity. Qed.
Definition OPSW : optable := plain_optable (fun _ _ _ _ => True) (fun _ _ => []) (fun _ _ _ _ _ _ _ h => h).

Definition PRIVW : list (int * int) := [(872448%uint63, 6492160%uint63)].
Definition image_region : region := Region 0%uint63 (VL wzero) true BGImage IMap.empty.
Definition stack_region (ROOM : Z) : region := Region (Uint63.of_Z (- ROOM)) (VL wzero) true BGNone IMap.empty.
Definition regsW (ROOM : Z) : IMap.t region := IMap.add 1%uint63 (stack_region ROOM) (IMap.add 0%uint63 image_region IMap.empty).
Definition wstate (ROOM : Z) (pc : int) (xf ff : rf sv) (facts : list fact) (next : int) : sstate :=
  SS pc xf ff RNone (regsW ROOM) facts [] PRIVW next.

Section I.
Variable ROOM : Z.
Hypothesis ROOMR : 0 < ROOM < 2 ^ 40.

Lemma regsW_bst : IMap.bst (regsW ROOM).
Proof. unfold regsW. apply IMap.bst_add, IMap.bst_add, IMap.bst_empty. Qed.

Lemma regsW_find : forall k r, IMap.find k (regsW ROOM) = Some r ->
  (k = 1%uint63 /\ r = stack_region ROOM) \/ (k = 0%uint63 /\ r = image_region).
Proof.
  intros k r H. unfold regsW in H.
  destruct (PrimInt63.eqb 1%uint63 k) eqn:K1.
  - apply Uint63.eqb_correct in K1. subst k. rewrite IMap.find_add_same in H by (apply IMap.bst_add, IMap.bst_empty). injection H as <-. left. auto.
  - rewrite IMap.find_add_other_eqb in H by (first [apply IMap.bst_add, IMap.bst_empty | exact K1]).
    destruct (PrimInt63.eqb 0%uint63 k) eqn:K0.
    + apply Uint63.eqb_correct in K0. subst k. rewrite IMap.find_add_same in H by apply IMap.bst_empty. injection H as <-. right. auto.
    + rewrite IMap.find_add_other_eqb in H by (first [apply IMap.bst_empty | exact K0]). rewrite IMap.find_empty in H. discriminate H.
Qed.

Lemma loZ_stack : loZ (stack_region ROOM) = - ROOM.
Proof. unfold loZ, stack_region. cbn [rg_lo]. apply GTwinSub.keyZ_of_Z. lia. Qed.
Lemma hiZ_stack : forall E, hiZ E (stack_region ROOM) = 0.
Proof. intros E. unfold hiZ, stack_region. cbn [rg_hi den]. reflexivity. Qed.

Lemma stack_region_ok : forall E (m : word -> option byte) lo,
  AF.stk bsegs m lo (bv_unsigned (ev E 1%uint63)) -> lo <= bv_unsigned (ev E 1%uint63) - ROOM -> 0x631000 <= lo ->
  region_ok bsegs PRIVW E m 1%uint63 (stack_region ROOM).
Proof.
  intros E m lo (S0 & S1 & SV) LO IMG.
  pose proof (bv_unsigned_in_range 64 (ev E 1%uint63)) as RB. rewrite bv_modulus_64 in RB. unfold W64.two64 in RB.
  constructor.
  - exact (@IMap.bst_empty gran).
  - intros _. rewrite loZ_stack, hiZ_stack. unfold two64. lia.
  - intros _ a Ha. rewrite loZ_stack, hiZ_stack in Ha.
    destruct (SV a ltac:(lia)) as [WV (b & RD)].
    split; [| split].
    + change (rb bsegs m a) with (AM.mrd bsegs m (AM.wa a)). rewrite RD. discriminate.
    + intros _. unfold wb. fold (AM.wa a). destruct (wview bsegs m (AM.wa a)); [reflexivity| contradiction].
    + apply ref_find_segment_none; lia.
  - intros g gr H. cbn [stack_region rg_cells] in H. rewrite IMap.find_empty in H. discriminate H.
  - intros g gr c i H. cbn [stack_region rg_cells] in H. rewrite IMap.find_empty in H. discriminate H.
  - intros o _ _ _. cbn [bg_byte stack_region rg_bg]. exact I.
Qed.

Lemma image_region_ok : forall E (m : word -> option byte),
  ev E 0%uint63 = Z_to_bv 64 0 -> AM.mem_inv bsegs m ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (AM.wa i) = None) ->
  region_ok bsegs PRIVW E m 0%uint63 image_region.
Proof.
  intros E m EZ MI RR. constructor.
  - exact (@IMap.bst_empty gran).
  - intros K; discriminate K.
  - intros K; discriminate K.
  - intros g gr H. cbn [image_region rg_cells] in H. rewrite IMap.find_empty in H. discriminate H.
  - intros g gr c i H. cbn [image_region rg_cells] in H. rewrite IMap.find_empty in H. discriminate H.
  - intros o _ H0 _. destruct (H0 eq_refl) as (OR & (bs & RD) & NP). cbn [bg_byte image_region rg_bg]. unfold img_byte.
    rewrite EZ. change (bv_unsigned (Z_to_bv 64 0)) with 0. rewrite Z.add_0_l.
    assert (O64 : 0 <= o < 2 ^ 64) by (unfold two63 in OR; lia).
    assert (UO : bv_unsigned (Z_to_bv 64 o) = o) by (rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
    assert (INIMG : 0x10000 <= o < 0x631000).
    { destruct (Z_lt_le_dec o 0x10000) as [L|L]; [| destruct (Z_lt_le_dec o 0x631000) as [L2|L2]; [lia|]].
      - rewrite (ref_memory_read_none (Z_to_bv 64 o) 1 ltac:(cbn; lia) ltac:(rewrite UO; cbn; lia)) in RD. discriminate RD.
      - rewrite (ref_memory_read_none (Z_to_bv 64 o) 1 ltac:(cbn; lia) ltac:(rewrite UO; cbn; lia)) in RD. discriminate RD. }
    assert (NPR : o < 0xd5000).
    { destruct (Z_lt_le_dec o 0xd5000) as [L|L]; [exact L|]. exfalso. apply NP. unfold in_priv, PRIVW.
      apply Exists_cons_hd. cbn [fst snd]. change (to_Z 872448%uint63) with 872448. change (to_Z 6492160%uint63) with 6492160. lia. }
    assert (MN : m (Z_to_bv 64 o) = None).
    { destruct (Z_lt_le_dec o 0xcf000) as [L|L].
      - destruct (m (Z_to_bv 64 o)) as [b|] eqn:MB; [| reflexivity]. exfalso.
        pose proof (MI _ _ MB) as RO. rewrite a_ro_addr, UO in RO.
        destruct (Z.leb_spec0 0x10000 o); destruct (Z.ltb_spec0 o 0xcf000); cbn in RO; try discriminate RO; lia.
      - apply (RR o). unfold ARELRO_LO, ARELRO_HI. lia. }
    destruct (rom_of bsegs (Z_to_bv 64 o)) as [b|] eqn:RM; [| exact I]. unfold rb. rewrite MN. exact RM.
Qed.

Theorem init_ok : forall E ms pc xf ff facts next lo,
  ms_pc_val ms = Z_to_bv 64 (to_Z pc) ->
  rf_get xf X0 = VL wzero ->
  (forall r, rget (core_of ms) (reg_of_r5 r) = den E (rf_get xf r)) ->
  (forall r, reg_get (ms_fregs ms) (reg_of_r5 r) = den E (rf_get ff r)) ->
  ms_svc_pending ms = None -> ms_resv ms = None -> bv_unsigned (ms_fcsr ms) < 32 -> ms_rom ms = rom_of bsegs ->
  ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E facts ->
  AF.stk bsegs (ms_mem ms) lo (bv_unsigned (ev E 1%uint63)) -> lo <= bv_unsigned (ev E 1%uint63) - ROOM -> 0x631000 <= lo ->
  AM.mem_inv bsegs (ms_mem ms) ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> ms_mem ms (AM.wa i) = None) ->
  st_ok bsegs OPSW E (wstate ROOM pc xf ff facts next) ms MOW.
Proof.
  intros E ms pc xf ff facts next lo HPC HX0 HR HF SVC RSV FC ROM EZ FH STK LO IMG MI RR.
  constructor; cbn [wstate s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next].
  - exact HPC.
  - exact HX0.
  - exact HR.
  - exact HF.
  - exact SVC.
  - cbn [resv_ok]. exact RSV.
  - exact FC.
  - exact ROM.
  - exact EZ.
  - exact regsW_bst.
  - intros k r H. destruct (regsW_find k r H) as [[-> ->]|[-> ->]].
    + exact (stack_region_ok E (ms_mem ms) lo STK LO IMG).
    + exact (image_region_ok E (ms_mem ms) EZ MI RR).
  - intros k1 r1 k2 r2 H1 H2 NE K1 K2 _ a _.
    destruct (regsW_find k1 r1 H1) as [[-> ->]|[-> ->]]; [| discriminate K1].
    destruct (regsW_find k2 r2 H2) as [[-> ->]|[-> ->]]; [apply NE; reflexivity| discriminate K2].
  - intros r g gr c H. destruct (regsW_find _ _ H) as [[X _]|[_ ->]]; [discriminate X|].
    intros HG. cbn [image_region rg_cells] in HG. rewrite IMap.find_empty in HG. discriminate HG.
  - exact FH.
  - unfold ops_hold. constructor.
  - unfold ops_apart. constructor.
  - exact MOW_facts.
  - intros a _. left. exact I.
  - intros a b MB seg FS. pose proof (MI _ _ MB) as RO. unfold AM.ro_addr in RO. rewrite FS in RO.
    destruct (seg_writable seg); [reflexivity| discriminate RO].
Qed.

End I.
End WInit.
End TwinB.
