(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import MemsetC MemOps.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS CtrLib MemsetC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Definition piece_chk (z : Z) : bool :=
  UnreggLib.bytes_eqb (store_bytes 8%uint63 (wbv (rep8 (of_Z z)))) (repeat (Z_to_bv 8 z) 8)
  && UnreggLib.bytes_eqb (store_bytes 1%uint63 (wbv (wlit (of_Z z)))) [Z_to_bv 8 z].
Lemma piece_chk_all : forallb piece_chk (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma piece_bytes : forall b, 0 <= to_Z b < 256 ->
  store_bytes 8%uint63 (wbv (rep8 b)) = repeat (Z_to_bv 8 (to_Z b)) 8 /\ store_bytes 1%uint63 (wbv (wlit b)) = [Z_to_bv 8 (to_Z b)].
Proof.
  intros b Hb. pose proof (proj1 (forallb_forall _ _) piece_chk_all (to_Z b)) as H.
  assert (IN : In (to_Z b) (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat (to_Z b)). split; [lia|]. apply in_seq. lia. }
  specialize (H IN). unfold piece_chk in H. rewrite Uint63.of_to_Z in H. apply andb_prop in H as [H1 H2].
  split; apply UnreggLib.bytes_eqb_eq; assumption.
Qed.

Module MemsetFX.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Lemma den_add_lit : forall E a (i : int), den E (sv_alu ALU_ADD a (VL (wlit i))) = (den E a + Z_to_bv 64 (to_Z i))%bv.
Proof. intros E a i. rewrite den_sv_alu. cbn [alu64 alu den]. unfold wbv. rewrite wlit_ok. reflexivity. Qed.

Lemma st_ok_self : forall E st ms mo, St.st_ok segs OPS E st ms mo -> St.st_ok segs OPS E st (ms_with_mem ms (ms_mem ms)) mo.
Proof.
  intros E st ms mo HS. pose proof HS as [_ _ _ _ Hsvc _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  destruct ms as [rg fr pcv svc rsv fc mm rom]. cbn in Hsvc. subst svc. exact HS.
Qed.

Lemma set_bytes_sound : forall fuel i dst ofs b len st stn E ms mo,
  St.st_ok segs OPS E st ms mo -> s_resv st = RNone -> ms_resv ms = None ->
  set_bytes segs fuel i dst ofs b len st = Some stn ->
  0 <= to_Z b < 256 -> to_Z i <= to_Z len <= 4096 ->
  let D := bv_unsigned (den E dst) in
  D + to_Z len < two64 ->
  exists m', St.st_ok segs OPS E stn (ms_with_mem ms m') mo
    /\ (forall a, 0 <= a < two64 -> ~ (D + to_Z i <= a < D + to_Z len) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a))
    /\ (forall j, to_Z i <= j < to_Z len -> m' (Z_to_bv 64 (D + j)) = Some (Z_to_bv 8 (to_Z b)))
    /\ (forall x, ms_mem ms x <> None -> m' x <> None)
    /\ s_pc stn = s_pc st /\ s_rf stn = s_rf st /\ s_ff stn = s_ff st /\ s_resv stn = RNone /\ s_facts stn = s_facts st
    /\ s_ops stn = s_ops st /\ s_priv stn = s_priv st /\ s_next stn = s_next st.
Proof.
  induction fuel as [|fuel IH]; intros i dst ofs b len st stn E ms mo HS RV MRV H Hb Hi D NW.
  - cbn [set_bytes] in H. destruct (PrimInt63.leb len i) eqn:L; [|discriminate H]. injection H as <-.
    apply Uint63.leb_spec in L. exists (ms_mem ms).
    split; [exact (st_ok_self E st ms mo HS)|].
    split; [intros; reflexivity|]. split; [intros j Hj; lia|]. split; [intros x Hx; exact Hx|]. repeat split; try reflexivity. exact RV.
  - cbn [set_bytes] in H. destruct (PrimInt63.leb len i) eqn:L.
    + injection H as <-. apply Uint63.leb_spec in L. exists (ms_mem ms).
      split; [exact (st_ok_self E st ms mo HS)|].
      split; [intros; reflexivity|]. split; [intros j Hj; lia|]. split; [intros x Hx; exact Hx|]. repeat split; try reflexivity. exact RV.
    + assert (LT : to_Z i < to_Z len) by (destruct (Uint63.lebP len i) as [Q|Q]; [discriminate L| lia]).
      pose proof (int_range i) as Ri. pose proof (int_range len) as Rl. rewrite two63_eq in Ri, Rl.
      assert (SUBE : to_Z (PrimInt63.sub len i) = to_Z len - to_Z i) by (rewrite Uint63.sub_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
      set (w8 := PrimInt63.leb 8%uint63 (PrimInt63.sub len i) && PrimInt63.eqb (PrimInt63.land (PrimInt63.add ofs i) 7%uint63) 0%uint63) in H.
      set (a := sv_alu ALU_ADD dst (VL (wlit i))) in H.
      assert (W8 : w8 = true -> 8 <= to_Z len - to_Z i).
      { intros Q. unfold w8 in Q. apply andb_prop in Q as [Q _]. apply Uint63.leb_spec in Q. rewrite SUBE in Q. change (to_Z 8%uint63) with 8 in Q. exact Q. }
      set (w := if w8 then 8%uint63 else 1%uint63) in H. set (v := if w8 then VL (rep8 b) else VL (wlit b)) in H.
      assert (WZ : to_Z w = if w8 then 8 else 1) by (unfold w; destruct w8; reflexivity).
      assert (Hw : wok w) by (unfold w, wok; destruct w8; [right; right; right; reflexivity | left; reflexivity]).
      destruct (do_store segs st a w v) as [st'|] eqn:DS; [|discriminate H].
      unfold do_store in DS. destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate DS].
      destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate DS].
      destruct (okey o) as [key|] eqn:Hk; [|discriminate DS].
      destruct (can_write segs (s_facts st) (s_priv st) k r key w) eqn:CW; [|discriminate DS].
      injection DS as <-. rewrite RV in H. cbn [resv_after_store] in H.
      destruct (store_sound segs OPS E st ms mo a k o r key w v RNone None HS Hw Ha Hr Hk CW eq_refl) as [SOK ST].
      replace (with_resv None (core_of ms)) with (core_of ms) in ST by (unfold with_resv, core_of; rewrite MRV; reflexivity).
      assert (DA : den E a = Z_to_bv 64 (D + to_Z i)).
      { unfold a. rewrite den_add_lit. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. fold D.
        rewrite (bv_wrap_small 64 (to_Z i)) by (unfold bv_modulus; lia). reflexivity. }
      set (bs := store_bytes w (den E v)) in *.
      assert (BS : bs = repeat (Z_to_bv 8 (to_Z b)) (Z.to_nat (to_Z w))).
      { unfold bs, v, w. destruct (piece_bytes b Hb) as [P8 P1]. destruct w8; cbn [den]; [rewrite P8| rewrite P1]; reflexivity. }
      assert (LBS : Z.of_nat (length bs) = to_Z w) by (rewrite BS, repeat_length; rewrite WZ; destruct w8; lia).
      set (m1 := write_to_mem (ms_mem ms) (den E a) bs) in *.
      assert (IW : to_Z (PrimInt63.add i w) = to_Z i + to_Z w).
      { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2 ^ 63). rewrite WZ. destruct w8; lia. }
      assert (WLE : to_Z i + to_Z w <= to_Z len) by (rewrite WZ; destruct w8 eqn:Q; [specialize (W8 eq_refl); lia| lia]).
      pose proof (bv_unsigned_in_range _ (den E dst)) as RD. unfold bv_modulus in RD. fold D in RD.
      destruct (IH (PrimInt63.add i w) dst ofs b len _ stn E (ms_with_mem ms m1) mo ST eq_refl MRV H Hb ltac:(rewrite IW; lia) NW)
        as (m' & HS' & FR' & IN' & MONO' & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
      exists m'. split; [exact HS'|]. cbn [ms_mem ms_with_mem ms_upd] in FR', MONO'. fold D in FR', IN'.
      split; [| split; [| split]].
      * intros x Hx NI. rewrite (FR' x Hx) by (rewrite IW; lia). unfold m1. rewrite DA.
        apply write_to_mem_frame; [lia | rewrite LBS; unfold two64 in *; lia | exact Hx | rewrite LBS; lia].
      * intros j Hj. destruct (Z_lt_le_dec j (to_Z i + to_Z w)) as [Q|Q].
        -- rewrite (FR' (D + j)) by (unfold two64 in *; rewrite ?IW; lia). unfold m1. rewrite DA.
           replace (D + j) with (D + to_Z i + (j - to_Z i)) by lia.
           rewrite write_to_mem_in by (rewrite ?LBS; unfold two64 in *; lia).
           rewrite BS. apply nth_error_repeat. rewrite <- LBS in Q. rewrite BS, repeat_length in Q. lia.
        -- apply IN'. rewrite IW. lia.
      * intros x Hx. apply MONO'. unfold m1. apply write_to_mem_mapped. exact Hx.
      * cbn [s_pc s_rf s_ff s_resv s_facts s_ops s_priv s_next] in F1, F2, F3, F5, F6, F7, F8. repeat split; assumption.
Qed.
End WithSegs.
End MemsetFX.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import MemsetC.TwinB MemOps.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS CtrLib MemsetC.TwinB.MemsetC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Definition piece_chk (z : Z) : bool :=
  UnreggLib.TwinB.bytes_eqb (store_bytes 8%uint63 (wbv (rep8 (of_Z z)))) (repeat (Z_to_bv 8 z) 8)
  && UnreggLib.TwinB.bytes_eqb (store_bytes 1%uint63 (wbv (wlit (of_Z z)))) [Z_to_bv 8 z].
Lemma piece_chk_all : forallb piece_chk (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma piece_bytes : forall b, 0 <= to_Z b < 256 ->
  store_bytes 8%uint63 (wbv (rep8 b)) = repeat (Z_to_bv 8 (to_Z b)) 8 /\ store_bytes 1%uint63 (wbv (wlit b)) = [Z_to_bv 8 (to_Z b)].
Proof.
  intros b Hb. pose proof (proj1 (forallb_forall _ _) piece_chk_all (to_Z b)) as H.
  assert (IN : In (to_Z b) (map Z.of_nat (seq 0 256))).
  { apply in_map_iff. exists (Z.to_nat (to_Z b)). split; [lia|]. apply in_seq. lia. }
  specialize (H IN). unfold piece_chk in H. rewrite Uint63.of_to_Z in H. apply andb_prop in H as [H1 H2].
  split; apply UnreggLib.TwinB.bytes_eqb_eq; assumption.
Qed.

Module MemsetFX.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Lemma den_add_lit : forall E a (i : int), den E (sv_alu ALU_ADD a (VL (wlit i))) = (den E a + Z_to_bv 64 (to_Z i))%bv.
Proof. intros E a i. rewrite den_sv_alu. cbn [alu64 alu den]. unfold wbv. rewrite wlit_ok. reflexivity. Qed.

Lemma st_ok_self : forall E st ms mo, St.st_ok segs OPS E st ms mo -> St.st_ok segs OPS E st (ms_with_mem ms (ms_mem ms)) mo.
Proof.
  intros E st ms mo HS. pose proof HS as [_ _ _ _ Hsvc _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  destruct ms as [rg fr pcv svc rsv fc mm rom]. cbn in Hsvc. subst svc. exact HS.
Qed.

Lemma set_bytes_sound : forall fuel i dst ofs b len st stn E ms mo,
  St.st_ok segs OPS E st ms mo -> s_resv st = RNone -> ms_resv ms = None ->
  set_bytes segs fuel i dst ofs b len st = Some stn ->
  0 <= to_Z b < 256 -> to_Z i <= to_Z len <= 4096 ->
  let D := bv_unsigned (den E dst) in
  D + to_Z len < two64 ->
  exists m', St.st_ok segs OPS E stn (ms_with_mem ms m') mo
    /\ (forall a, 0 <= a < two64 -> ~ (D + to_Z i <= a < D + to_Z len) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a))
    /\ (forall j, to_Z i <= j < to_Z len -> m' (Z_to_bv 64 (D + j)) = Some (Z_to_bv 8 (to_Z b)))
    /\ (forall x, ms_mem ms x <> None -> m' x <> None)
    /\ s_pc stn = s_pc st /\ s_rf stn = s_rf st /\ s_ff stn = s_ff st /\ s_resv stn = RNone /\ s_facts stn = s_facts st
    /\ s_ops stn = s_ops st /\ s_priv stn = s_priv st /\ s_next stn = s_next st.
Proof.
  induction fuel as [|fuel IH]; intros i dst ofs b len st stn E ms mo HS RV MRV H Hb Hi D NW.
  - cbn [set_bytes] in H. destruct (PrimInt63.leb len i) eqn:L; [|discriminate H]. injection H as <-.
    apply Uint63.leb_spec in L. exists (ms_mem ms).
    split; [exact (st_ok_self E st ms mo HS)|].
    split; [intros; reflexivity|]. split; [intros j Hj; lia|]. split; [intros x Hx; exact Hx|]. repeat split; try reflexivity. exact RV.
  - cbn [set_bytes] in H. destruct (PrimInt63.leb len i) eqn:L.
    + injection H as <-. apply Uint63.leb_spec in L. exists (ms_mem ms).
      split; [exact (st_ok_self E st ms mo HS)|].
      split; [intros; reflexivity|]. split; [intros j Hj; lia|]. split; [intros x Hx; exact Hx|]. repeat split; try reflexivity. exact RV.
    + assert (LT : to_Z i < to_Z len) by (destruct (Uint63.lebP len i) as [Q|Q]; [discriminate L| lia]).
      pose proof (int_range i) as Ri. pose proof (int_range len) as Rl. rewrite two63_eq in Ri, Rl.
      assert (SUBE : to_Z (PrimInt63.sub len i) = to_Z len - to_Z i) by (rewrite Uint63.sub_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
      set (w8 := PrimInt63.leb 8%uint63 (PrimInt63.sub len i) && PrimInt63.eqb (PrimInt63.land (PrimInt63.add ofs i) 7%uint63) 0%uint63) in H.
      set (a := sv_alu ALU_ADD dst (VL (wlit i))) in H.
      assert (W8 : w8 = true -> 8 <= to_Z len - to_Z i).
      { intros Q. unfold w8 in Q. apply andb_prop in Q as [Q _]. apply Uint63.leb_spec in Q. rewrite SUBE in Q. change (to_Z 8%uint63) with 8 in Q. exact Q. }
      set (w := if w8 then 8%uint63 else 1%uint63) in H. set (v := if w8 then VL (rep8 b) else VL (wlit b)) in H.
      assert (WZ : to_Z w = if w8 then 8 else 1) by (unfold w; destruct w8; reflexivity).
      assert (Hw : wok w) by (unfold w, wok; destruct w8; [right; right; right; reflexivity | left; reflexivity]).
      destruct (do_store segs st a w v) as [st'|] eqn:DS; [|discriminate H].
      unfold do_store in DS. destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate DS].
      destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate DS].
      destruct (okey o) as [key|] eqn:Hk; [|discriminate DS].
      destruct (can_write segs (s_facts st) (s_priv st) k r key w) eqn:CW; [|discriminate DS].
      injection DS as <-. rewrite RV in H. cbn [resv_after_store] in H.
      destruct (store_sound segs OPS E st ms mo a k o r key w v RNone None HS Hw Ha Hr Hk CW eq_refl) as [SOK ST].
      replace (with_resv None (core_of ms)) with (core_of ms) in ST by (unfold with_resv, core_of; rewrite MRV; reflexivity).
      assert (DA : den E a = Z_to_bv 64 (D + to_Z i)).
      { unfold a. rewrite den_add_lit. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. fold D.
        rewrite (bv_wrap_small 64 (to_Z i)) by (unfold bv_modulus; lia). reflexivity. }
      set (bs := store_bytes w (den E v)) in *.
      assert (BS : bs = repeat (Z_to_bv 8 (to_Z b)) (Z.to_nat (to_Z w))).
      { unfold bs, v, w. destruct (piece_bytes b Hb) as [P8 P1]. destruct w8; cbn [den]; [rewrite P8| rewrite P1]; reflexivity. }
      assert (LBS : Z.of_nat (length bs) = to_Z w) by (rewrite BS, repeat_length; rewrite WZ; destruct w8; lia).
      set (m1 := write_to_mem (ms_mem ms) (den E a) bs) in *.
      assert (IW : to_Z (PrimInt63.add i w) = to_Z i + to_Z w).
      { rewrite Uint63.add_spec. apply Z.mod_small. change wB with (2 ^ 63). rewrite WZ. destruct w8; lia. }
      assert (WLE : to_Z i + to_Z w <= to_Z len) by (rewrite WZ; destruct w8 eqn:Q; [specialize (W8 eq_refl); lia| lia]).
      pose proof (bv_unsigned_in_range _ (den E dst)) as RD. unfold bv_modulus in RD. fold D in RD.
      destruct (IH (PrimInt63.add i w) dst ofs b len _ stn E (ms_with_mem ms m1) mo ST eq_refl MRV H Hb ltac:(rewrite IW; lia) NW)
        as (m' & HS' & FR' & IN' & MONO' & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
      exists m'. split; [exact HS'|]. cbn [ms_mem ms_with_mem ms_upd] in FR', MONO'. fold D in FR', IN'.
      split; [| split; [| split]].
      * intros x Hx NI. rewrite (FR' x Hx) by (rewrite IW; lia). unfold m1. rewrite DA.
        apply write_to_mem_frame; [lia | rewrite LBS; unfold two64 in *; lia | exact Hx | rewrite LBS; lia].
      * intros j Hj. destruct (Z_lt_le_dec j (to_Z i + to_Z w)) as [Q|Q].
        -- rewrite (FR' (D + j)) by (unfold two64 in *; rewrite ?IW; lia). unfold m1. rewrite DA.
           replace (D + j) with (D + to_Z i + (j - to_Z i)) by lia.
           rewrite write_to_mem_in by (rewrite ?LBS; unfold two64 in *; lia).
           rewrite BS. apply nth_error_repeat. rewrite <- LBS in Q. rewrite BS, repeat_length in Q. lia.
        -- apply IN'. rewrite IW. lia.
      * intros x Hx. apply MONO'. unfold m1. apply write_to_mem_mapped. exact Hx.
      * cbn [s_pc s_rf s_ff s_resv s_facts s_ops s_priv s_next] in F1, F2, F3, F5, F6, F7, F8. repeat split; assumption.
Qed.
End WithSegs.
End MemsetFX.
End TwinB.
