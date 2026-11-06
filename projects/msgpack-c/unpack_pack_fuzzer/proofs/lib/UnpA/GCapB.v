(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp GCap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GCapB.

Definition CAPS6 : list int := [256; 512; 1024; 2048; 4096; 8192]%uint63.
Definition BOUNDw : w64 := wlit 8192%uint63.

Lemma cap32_le1024 : forall c, cap32_b c = true -> c <= 1024 -> c = 32 \/ c = 64 \/ c = 128 \/ c = 256 \/ c = 512 \/ c = 1024.
Proof.
  intros c H LE. unfold cap32_b, EMBED_STACK in H. apply andb_prop in H as [H P2]. apply andb_prop in H as [GE MD].
  apply Z.leb_le in GE. apply Z.eqb_eq in MD. apply pow2_b_spec in P2 as (k & Hk & Hq).
  assert (C : c = 32 * 2 ^ k) by (rewrite <- Hq; pose proof (Z.div_mod c 32 ltac:(lia)); lia).
  assert (K6 : k < 6).
  { destruct (Z_lt_ge_dec k 6) as [|G]; [assumption|]. exfalso.
    pose proof (Z.pow_le_mono_r 2 6 k ltac:(lia) ltac:(lia)) as X. change (2 ^ 6) with 64 in X. lia. }
  assert (KK : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia.
  destruct KK as [->|[->|[->|[->|[->| ->]]]]]; subst c;
    [left| right; left| right; right; left| right; right; right; left| right; right; right; right; left| right; right; right; right; right]; reflexivity.
Qed.

Section WithPc.
Variable CAP_PC : int.
Variable isV : bool.

Definition IB : nat := if isV then 4%nat else 1%nat.
Definition IC : nat := if isV then 6%nat else 3%nat.

Definition gcapb_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 || PrimInt63.eqb md 2%uint63 then
        match GCap.carg ca IB with
        | VP kB ob =>
            let fs := s_facts st in let cap := GCap.carg ca IC in
            if weqb ob wzero && implied fs (FULe cap (VP kB BOUNDw)) && nowrap_kb fs kB BOUNDw
            then Some (map (GCap.post st kB cap) CAPS6)
            else None
        | _ => None
        end
      else None
  | None => None
  end.

Definition gcapb_contract : contract := Contract CAP_PC gcapb_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma split_b : forall E st ms model md aw ws ca kB ob,
  st_ok segs OPS E st ms model -> the_op st = Some (md, aw, ws, ca) -> (md = 1%uint63 \/ md = 2%uint63) ->
  GCap.carg ca IB = VP kB ob -> weqb ob wzero = true ->
  bv_unsigned (den E (GCap.carg ca IC)) <= bv_unsigned (ev E kB) + 8192 ->
  exists L, In L CAPS6 /\ bv_unsigned (den E (GCap.carg ca IC)) = bv_unsigned (ev E kB) + to_Z L.
Proof.
  intros E st ms model md aw ws ca kB ob HS TO MD EB OB LE.
  pose proof (so_ops _ _ _ _ _ _ HS) as Pops.
  destruct (the_op_sound E st md aw ws _ TO) as (o & OPS1 & OID & DEC & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md0 & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC). rewrite DEC in DEC0. injection DEC0 as <- <- <- <-.
  assert (HC' : exists u, decode_uc (map (den E) ca) = Some u /\ unp_client segs (to_Z md) u LB (map (wden E) ws) (ms_mem ms)).
  { cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC.
    destruct MD as [-> | ->]; [change (to_Z 1%uint63) with 1 in *| change (to_Z 2%uint63) with 2 in *];
      cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC;
      (destruct (decode_uc (map (den E) ca)) as [u|]; [exists u; split; [reflexivity| exact HC]| contradiction]). }
  destruct HC' as (u & DU & HCu).
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate DU.
  cbn [map decode_uc] in DU. injection DU as <-.
  destruct HCu as (g & L & P & _).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & _).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap.
  pose proof P as (VC & EC & SC & CC & VV & EV & SV' & CV & _).
  set (V := if isV then u_vstk g else u_cstk g).
  assert (VF : v_elt V = 8 /\ cap32_b (v_cap V) = true /\
               v_begin V = bv_unsigned (den E (VP kB ob)) /\
               v_capend V = bv_unsigned (den E (GCap.carg [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] IC))).
  { subst V. unfold IB, IC in *. destruct isV; cbn [GCap.carg nth] in EB |- *; rewrite <- EB.
    - repeat split; [exact EV| exact CV| exact Lvb| exact Lvcap].
    - repeat split; [exact EC| exact CC| exact Lcb| exact Lccap]. }
  destruct VF as (VELT & VCAP & LVB & LVC).
  rewrite (den_VP0 E kB ob OB) in LVB.
  assert (DCAP : bv_unsigned (den E (GCap.carg [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] IC))
                 = bv_unsigned (ev E kB) + 8 * v_cap V).
  { rewrite <- LVC. unfold v_capend. rewrite VELT, LVB. reflexivity. }
  assert (C1024 : v_cap V <= 1024) by (rewrite DCAP in LE; lia).
  destruct (cap32_le1024 _ VCAP C1024) as [C|[C|[C|[C|[C|C]]]]]; rewrite C in DCAP.
  - exists 256%uint63. split; [cbn [CAPS6 In]; tauto| exact DCAP].
  - exists 512%uint63. split; [cbn [CAPS6 In]; tauto| exact DCAP].
  - exists 1024%uint63. split; [cbn [CAPS6 In]; tauto| exact DCAP].
  - exists 2048%uint63. split; [cbn [CAPS6 In]; tauto| exact DCAP].
  - exists 4096%uint63. split; [cbn [CAPS6 In]; tauto| exact DCAP].
  - exists 8192%uint63. split; [cbn [CAPS6 In]; tauto| exact DCAP].
Qed.

Theorem gcapb_sound : contract_sound segs OPS MP PB gcapb_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gcapb_contract c_apply] in HA. unfold gcapb_apply in HA.
  pose proof (so_zero _ _ _ _ _ _ HS) as Pz. pose proof (so_facts _ _ _ _ _ _ HS) as Pfacts.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1%uint63 || PrimInt63.eqb mdi 2%uint63) eqn:EMD; [|discriminate].
  assert (MD : mdi = 1%uint63 \/ mdi = 2%uint63) by (apply orb_prop in EMD as [M|M]; apply Uint63.eqb_correct in M; [left| right]; exact M).
  destruct (GCap.carg ca IB) as [|kB ob| | | | | | | | |] eqn:EB; try discriminate.
  cbv zeta in HA.
  match type of HA with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection HA as <-.
  apply andb_prop in COND as [COND NW]. apply andb_prop in COND as [OB IMP].
  pose proof (implied_sound E (s_facts st) _ Pz Pfacts IMP) as I1. cbn [fact_holds] in I1.
  destruct (nowrap_kb_sound E (s_facts st) Pfacts kB BOUNDw NW) as [_ DV].
  assert (LE : bv_unsigned (den E (GCap.carg ca IC)) <= bv_unsigned (ev E kB) + 8192).
  { rewrite DV in I1. exact I1. }
  destruct (split_b E st ms model mdi aw ws ca kB ob HS TO MD EB OB LE) as (L & INL & DCAP).
  apply (Hk (GCap.post st kB (GCap.carg ca IC) L) (in_map _ _ _ INL) E ms model (env_ext_refl _ E) HMP).
  - exact (GCap.post_sound segs OPS MP E st ms model kB _ L HS DCAP).
Qed.

End Sound.
End WithPc.

Definition PAIRS : list (int * int) :=
  [(256, 256); (256, 512); (512, 512); (512, 1024); (1024, 1024); (1024, 2048); (2048, 2048); (2048, 4096); (4096, 4096); (4096, 8192); (8192, 8192)]%uint63.

Lemma pairs_complete : forall c v,
  (c = 32 \/ c = 64 \/ c = 128 \/ c = 256 \/ c = 512 \/ c = 1024) -> (v = c \/ v = 2 * c) -> v <= 1024 ->
  exists p, In p PAIRS /\ 8 * c = to_Z (fst p) /\ 8 * v = to_Z (snd p).
Proof.
  intros c v HC HV LE.
  destruct HC as [->|[->|[->|[->|[->| ->]]]]]; destruct HV as [-> | ->]; try (exfalso; lia);
    match goal with |- exists p, In p PAIRS /\ ?a = _ /\ ?b = _ =>
      exists (Uint63.of_Z a, Uint63.of_Z b); split; [vm_compute; repeat (first [left; reflexivity| right])| split; vm_compute; reflexivity] end.
Qed.

Section Pair.
Variable CAP_PC : int.

Definition post2 (st : sstate) (kC : int) (ccap : sv) (kV : int) (vcap : sv) (p : int * int) : sstate :=
  GCap.post (GCap.post st kC ccap (fst p)) kV vcap (snd p).

Definition gcapb2_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 || PrimInt63.eqb md 2%uint63 then
        match GCap.carg ca 1%nat, GCap.carg ca 4%nat with
        | VP kC oc, VP kV ov =>
            let fs := s_facts st in let ccap := GCap.carg ca 3%nat in let vcap := GCap.carg ca 6%nat in
            if weqb oc wzero && weqb ov wzero
               && implied fs (FULe ccap (VP kC BOUNDw)) && nowrap_kb fs kC BOUNDw
               && implied fs (FULe vcap (VP kV BOUNDw)) && nowrap_kb fs kV BOUNDw
            then Some (map (post2 st kC ccap kV vcap) PAIRS)
            else None
        | _, _ => None
        end
      else None
  | None => None
  end.

Definition gcapb2_contract : contract := Contract CAP_PC gcapb2_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma split2 : forall E st ms model md aw ws ca kC oc kV ov,
  st_ok segs OPS E st ms model -> the_op st = Some (md, aw, ws, ca) -> (md = 1%uint63 \/ md = 2%uint63) ->
  GCap.carg ca 1%nat = VP kC oc -> weqb oc wzero = true -> GCap.carg ca 4%nat = VP kV ov -> weqb ov wzero = true ->
  bv_unsigned (den E (GCap.carg ca 3%nat)) <= bv_unsigned (ev E kC) + 8192 ->
  bv_unsigned (den E (GCap.carg ca 6%nat)) <= bv_unsigned (ev E kV) + 8192 ->
  exists p, In p PAIRS /\ bv_unsigned (den E (GCap.carg ca 3%nat)) = bv_unsigned (ev E kC) + to_Z (fst p)
                       /\ bv_unsigned (den E (GCap.carg ca 6%nat)) = bv_unsigned (ev E kV) + to_Z (snd p).
Proof.
  intros E st ms model md aw ws ca kC oc kV ov HS TO MD EC OC EV OV LEc LEv.
  pose proof (so_ops _ _ _ _ _ _ HS) as Pops.
  destruct (the_op_sound E st md aw ws _ TO) as (o & OPS1 & OID & DEC & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md0 & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC). rewrite DEC in DEC0. injection DEC0 as <- <- <- <-.
  assert (HC' : exists u, decode_uc (map (den E) ca) = Some u /\ unp_client segs (to_Z md) u LB (map (wden E) ws) (ms_mem ms)).
  { cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC.
    destruct MD as [-> | ->]; [change (to_Z 1%uint63) with 1 in *| change (to_Z 2%uint63) with 2 in *];
      cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC;
      (destruct (decode_uc (map (den E) ca)) as [u|]; [exists u; split; [reflexivity| exact HC]| contradiction]). }
  destruct HC' as (u & DU & HCu).
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate DU.
  cbn [map decode_uc] in DU. injection DU as <-.
  destruct HCu as (g & L & P & O & _).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & _).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap.
  pose proof P as (VC & ELC & SC & CC & VV & ELV & SV' & CV & _).
  pose proof (own_tied g LB O) as TIE. unfold v_bytes in TIE. rewrite ELC, ELV in TIE.
  cbn [GCap.carg nth] in EC, EV, LEc, LEv |- *. subst cb vb.
  rewrite (den_VP0 E kC oc OC) in Lcb. rewrite (den_VP0 E kV ov OV) in Lvb.
  assert (DC : bv_unsigned (den E ccap) = bv_unsigned (ev E kC) + 8 * v_cap (u_cstk g)) by (rewrite <- Lccap; unfold v_capend; rewrite ELC, Lcb; reflexivity).
  assert (DV : bv_unsigned (den E vcap) = bv_unsigned (ev E kV) + 8 * v_cap (u_vstk g)) by (rewrite <- Lvcap; unfold v_capend; rewrite ELV, Lvb; reflexivity).
  assert (C1024 : v_cap (u_cstk g) <= 1024) by (rewrite DC in LEc; lia).
  assert (V1024 : v_cap (u_vstk g) <= 1024) by (rewrite DV in LEv; lia).
  rewrite DC, DV.
  assert (VC2 : v_cap (u_vstk g) = v_cap (u_cstk g) \/ v_cap (u_vstk g) = 2 * v_cap (u_cstk g)) by (clear - TIE; lia).
  destruct (pairs_complete _ _ (cap32_le1024 _ CC C1024) VC2 V1024) as (p & INP & E1 & E2).
  exists p. split; [exact INP|]. rewrite E1, E2. split; reflexivity.
Qed.

Theorem gcapb2_sound : contract_sound segs OPS MP PB gcapb2_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gcapb2_contract c_apply] in HA. unfold gcapb2_apply in HA.
  pose proof (so_zero _ _ _ _ _ _ HS) as Pz. pose proof (so_facts _ _ _ _ _ _ HS) as Pfacts.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1%uint63 || PrimInt63.eqb mdi 2%uint63) eqn:EMD; [|discriminate].
  assert (MD : mdi = 1%uint63 \/ mdi = 2%uint63) by (apply orb_prop in EMD as [M|M]; apply Uint63.eqb_correct in M; [left| right]; exact M).
  destruct (GCap.carg ca 1%nat) as [|kC oc| | | | | | | | |] eqn:EC; try discriminate.
  destruct (GCap.carg ca 4%nat) as [|kV ov| | | | | | | | |] eqn:EV; try discriminate.
  cbv zeta in HA.
  match type of HA with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection HA as <-.
  apply andb_prop in COND as [COND NWv]. apply andb_prop in COND as [COND IMPv]. apply andb_prop in COND as [COND NWc].
  apply andb_prop in COND as [COND IMPc]. apply andb_prop in COND as [OC OV].
  pose proof (implied_sound E (s_facts st) _ Pz Pfacts IMPc) as Ic. pose proof (implied_sound E (s_facts st) _ Pz Pfacts IMPv) as Iv. cbn [fact_holds] in Ic, Iv.
  destruct (nowrap_kb_sound E (s_facts st) Pfacts kC BOUNDw NWc) as [_ DVc]. destruct (nowrap_kb_sound E (s_facts st) Pfacts kV BOUNDw NWv) as [_ DVv].
  rewrite DVc in Ic. rewrite DVv in Iv.
  destruct (split2 E st ms model mdi aw ws ca kC oc kV ov HS TO MD EC OC EV OV Ic Iv) as (p & INP & DCAPc & DCAPv).
  apply (Hk (post2 st kC (GCap.carg ca 3%nat) kV (GCap.carg ca 6%nat) p) (in_map _ _ _ INP) E ms model (env_ext_refl _ E) HMP).
  - unfold post2. apply (GCap.post_sound segs OPS MP E _ ms model kV _ (snd p)); [| exact DCAPv].
    exact (GCap.post_sound segs OPS MP E st ms model kC _ (fst p) HS DCAPc).
Qed.

End Sound.
End Pair.
End GCapB.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Model OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Arith OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Steps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GUnp OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GCap.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GCapB.

Definition CAPS6 : list int := [256; 512; 1024; 2048; 4096; 8192]%uint63.
Definition BOUNDw : w64 := wlit 8192%uint63.

Lemma cap32_le1024 : forall c, cap32_b c = true -> c <= 1024 -> c = 32 \/ c = 64 \/ c = 128 \/ c = 256 \/ c = 512 \/ c = 1024.
Proof.
  intros c H LE. unfold cap32_b, EMBED_STACK in H. apply andb_prop in H as [H P2]. apply andb_prop in H as [GE MD].
  apply Z.leb_le in GE. apply Z.eqb_eq in MD. apply pow2_b_spec in P2 as (k & Hk & Hq).
  assert (C : c = 32 * 2 ^ k) by (rewrite <- Hq; pose proof (Z.div_mod c 32 ltac:(lia)); lia).
  assert (K6 : k < 6).
  { destruct (Z_lt_ge_dec k 6) as [|G]; [assumption|]. exfalso.
    pose proof (Z.pow_le_mono_r 2 6 k ltac:(lia) ltac:(lia)) as X. change (2 ^ 6) with 64 in X. lia. }
  assert (KK : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia.
  destruct KK as [->|[->|[->|[->|[->| ->]]]]]; subst c;
    [left| right; left| right; right; left| right; right; right; left| right; right; right; right; left| right; right; right; right; right]; reflexivity.
Qed.

Section WithPc.
Variable CAP_PC : int.
Variable isV : bool.

Definition IB : nat := if isV then 4%nat else 1%nat.
Definition IC : nat := if isV then 6%nat else 3%nat.

Definition gcapb_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 || PrimInt63.eqb md 2%uint63 then
        match GCap.carg ca IB with
        | VP kB ob =>
            let fs := s_facts st in let cap := GCap.carg ca IC in
            if weqb ob wzero && implied fs (FULe cap (VP kB BOUNDw)) && nowrap_kb fs kB BOUNDw
            then Some (map (GCap.post st kB cap) CAPS6)
            else None
        | _ => None
        end
      else None
  | None => None
  end.

Definition gcapb_contract : contract := Contract CAP_PC gcapb_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma split_b : forall E st ms model md aw ws ca kB ob,
  st_ok segs OPS E st ms model -> the_op st = Some (md, aw, ws, ca) -> (md = 1%uint63 \/ md = 2%uint63) ->
  GCap.carg ca IB = VP kB ob -> weqb ob wzero = true ->
  bv_unsigned (den E (GCap.carg ca IC)) <= bv_unsigned (ev E kB) + 8192 ->
  exists L, In L CAPS6 /\ bv_unsigned (den E (GCap.carg ca IC)) = bv_unsigned (ev E kB) + to_Z L.
Proof.
  intros E st ms model md aw ws ca kB ob HS TO MD EB OB LE.
  pose proof (so_ops _ _ _ _ _ _ HS) as Pops.
  destruct (the_op_sound E st md aw ws _ TO) as (o & OPS1 & OID & DEC & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md0 & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC). rewrite DEC in DEC0. injection DEC0 as <- <- <- <-.
  assert (HC' : exists u, decode_uc (map (den E) ca) = Some u /\ unp_client segs (to_Z md) u LB (map (wden E) ws) (ms_mem ms)).
  { cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC.
    destruct MD as [-> | ->]; [change (to_Z 1%uint63) with 1 in *| change (to_Z 2%uint63) with 2 in *];
      cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC;
      (destruct (decode_uc (map (den E) ca)) as [u|]; [exists u; split; [reflexivity| exact HC]| contradiction]). }
  destruct HC' as (u & DU & HCu).
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate DU.
  cbn [map decode_uc] in DU. injection DU as <-.
  destruct HCu as (g & L & P & _).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & _).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap.
  pose proof P as (VC & EC & SC & CC & VV & EV & SV' & CV & _).
  set (V := if isV then u_vstk g else u_cstk g).
  assert (VF : v_elt V = 8 /\ cap32_b (v_cap V) = true /\
               v_begin V = bv_unsigned (den E (VP kB ob)) /\
               v_capend V = bv_unsigned (den E (GCap.carg [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] IC))).
  { subst V. unfold IB, IC in *. destruct isV; cbn [GCap.carg nth] in EB |- *; rewrite <- EB.
    - repeat split; [exact EV| exact CV| exact Lvb| exact Lvcap].
    - repeat split; [exact EC| exact CC| exact Lcb| exact Lccap]. }
  destruct VF as (VELT & VCAP & LVB & LVC).
  rewrite (den_VP0 E kB ob OB) in LVB.
  assert (DCAP : bv_unsigned (den E (GCap.carg [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] IC))
                 = bv_unsigned (ev E kB) + 8 * v_cap V).
  { rewrite <- LVC. unfold v_capend. rewrite VELT, LVB. reflexivity. }
  assert (C1024 : v_cap V <= 1024) by (rewrite DCAP in LE; lia).
  destruct (cap32_le1024 _ VCAP C1024) as [C|[C|[C|[C|[C|C]]]]]; rewrite C in DCAP.
  - exists 256%uint63. split; [cbn [CAPS6 In]; tauto| exact DCAP].
  - exists 512%uint63. split; [cbn [CAPS6 In]; tauto| exact DCAP].
  - exists 1024%uint63. split; [cbn [CAPS6 In]; tauto| exact DCAP].
  - exists 2048%uint63. split; [cbn [CAPS6 In]; tauto| exact DCAP].
  - exists 4096%uint63. split; [cbn [CAPS6 In]; tauto| exact DCAP].
  - exists 8192%uint63. split; [cbn [CAPS6 In]; tauto| exact DCAP].
Qed.

Theorem gcapb_sound : contract_sound segs OPS MP PB gcapb_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gcapb_contract c_apply] in HA. unfold gcapb_apply in HA.
  pose proof (so_zero _ _ _ _ _ _ HS) as Pz. pose proof (so_facts _ _ _ _ _ _ HS) as Pfacts.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1%uint63 || PrimInt63.eqb mdi 2%uint63) eqn:EMD; [|discriminate].
  assert (MD : mdi = 1%uint63 \/ mdi = 2%uint63) by (apply orb_prop in EMD as [M|M]; apply Uint63.eqb_correct in M; [left| right]; exact M).
  destruct (GCap.carg ca IB) as [|kB ob| | | | | | | | |] eqn:EB; try discriminate.
  cbv zeta in HA.
  match type of HA with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection HA as <-.
  apply andb_prop in COND as [COND NW]. apply andb_prop in COND as [OB IMP].
  pose proof (implied_sound E (s_facts st) _ Pz Pfacts IMP) as I1. cbn [fact_holds] in I1.
  destruct (nowrap_kb_sound E (s_facts st) Pfacts kB BOUNDw NW) as [_ DV].
  assert (LE : bv_unsigned (den E (GCap.carg ca IC)) <= bv_unsigned (ev E kB) + 8192).
  { rewrite DV in I1. exact I1. }
  destruct (split_b E st ms model mdi aw ws ca kB ob HS TO MD EB OB LE) as (L & INL & DCAP).
  apply (Hk (GCap.post st kB (GCap.carg ca IC) L) (in_map _ _ _ INL) E ms model (env_ext_refl _ E) HMP).
  - exact (GCap.post_sound segs OPS MP E st ms model kB _ L HS DCAP).
Qed.

End Sound.
End WithPc.

Definition PAIRS : list (int * int) :=
  [(256, 256); (256, 512); (512, 512); (512, 1024); (1024, 1024); (1024, 2048); (2048, 2048); (2048, 4096); (4096, 4096); (4096, 8192); (8192, 8192)]%uint63.

Lemma pairs_complete : forall c v,
  (c = 32 \/ c = 64 \/ c = 128 \/ c = 256 \/ c = 512 \/ c = 1024) -> (v = c \/ v = 2 * c) -> v <= 1024 ->
  exists p, In p PAIRS /\ 8 * c = to_Z (fst p) /\ 8 * v = to_Z (snd p).
Proof.
  intros c v HC HV LE.
  destruct HC as [->|[->|[->|[->|[->| ->]]]]]; destruct HV as [-> | ->]; try (exfalso; lia);
    match goal with |- exists p, In p PAIRS /\ ?a = _ /\ ?b = _ =>
      exists (Uint63.of_Z a, Uint63.of_Z b); split; [vm_compute; repeat (first [left; reflexivity| right])| split; vm_compute; reflexivity] end.
Qed.

Section Pair.
Variable CAP_PC : int.

Definition post2 (st : sstate) (kC : int) (ccap : sv) (kV : int) (vcap : sv) (p : int * int) : sstate :=
  GCap.post (GCap.post st kC ccap (fst p)) kV vcap (snd p).

Definition gcapb2_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 || PrimInt63.eqb md 2%uint63 then
        match GCap.carg ca 1%nat, GCap.carg ca 4%nat with
        | VP kC oc, VP kV ov =>
            let fs := s_facts st in let ccap := GCap.carg ca 3%nat in let vcap := GCap.carg ca 6%nat in
            if weqb oc wzero && weqb ov wzero
               && implied fs (FULe ccap (VP kC BOUNDw)) && nowrap_kb fs kC BOUNDw
               && implied fs (FULe vcap (VP kV BOUNDw)) && nowrap_kb fs kV BOUNDw
            then Some (map (post2 st kC ccap kV vcap) PAIRS)
            else None
        | _, _ => None
        end
      else None
  | None => None
  end.

Definition gcapb2_contract : contract := Contract CAP_PC gcapb2_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma split2 : forall E st ms model md aw ws ca kC oc kV ov,
  st_ok segs OPS E st ms model -> the_op st = Some (md, aw, ws, ca) -> (md = 1%uint63 \/ md = 2%uint63) ->
  GCap.carg ca 1%nat = VP kC oc -> weqb oc wzero = true -> GCap.carg ca 4%nat = VP kV ov -> weqb ov wzero = true ->
  bv_unsigned (den E (GCap.carg ca 3%nat)) <= bv_unsigned (ev E kC) + 8192 ->
  bv_unsigned (den E (GCap.carg ca 6%nat)) <= bv_unsigned (ev E kV) + 8192 ->
  exists p, In p PAIRS /\ bv_unsigned (den E (GCap.carg ca 3%nat)) = bv_unsigned (ev E kC) + to_Z (fst p)
                       /\ bv_unsigned (den E (GCap.carg ca 6%nat)) = bv_unsigned (ev E kV) + to_Z (snd p).
Proof.
  intros E st ms model md aw ws ca kC oc kV ov HS TO MD EC OC EV OV LEc LEv.
  pose proof (so_ops _ _ _ _ _ _ HS) as Pops.
  destruct (the_op_sound E st md aw ws _ TO) as (o & OPS1 & OID & DEC & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md0 & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC). rewrite DEC in DEC0. injection DEC0 as <- <- <- <-.
  assert (HC' : exists u, decode_uc (map (den E) ca) = Some u /\ unp_client segs (to_Z md) u LB (map (wden E) ws) (ms_mem ms)).
  { cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC.
    destruct MD as [-> | ->]; [change (to_Z 1%uint63) with 1 in *| change (to_Z 2%uint63) with 2 in *];
      cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC;
      (destruct (decode_uc (map (den E) ca)) as [u|]; [exists u; split; [reflexivity| exact HC]| contradiction]). }
  destruct HC' as (u & DU & HCu).
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate DU.
  cbn [map decode_uc] in DU. injection DU as <-.
  destruct HCu as (g & L & P & O & _).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & _).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap.
  pose proof P as (VC & ELC & SC & CC & VV & ELV & SV' & CV & _).
  pose proof (own_tied g LB O) as TIE. unfold v_bytes in TIE. rewrite ELC, ELV in TIE.
  cbn [GCap.carg nth] in EC, EV, LEc, LEv |- *. subst cb vb.
  rewrite (den_VP0 E kC oc OC) in Lcb. rewrite (den_VP0 E kV ov OV) in Lvb.
  assert (DC : bv_unsigned (den E ccap) = bv_unsigned (ev E kC) + 8 * v_cap (u_cstk g)) by (rewrite <- Lccap; unfold v_capend; rewrite ELC, Lcb; reflexivity).
  assert (DV : bv_unsigned (den E vcap) = bv_unsigned (ev E kV) + 8 * v_cap (u_vstk g)) by (rewrite <- Lvcap; unfold v_capend; rewrite ELV, Lvb; reflexivity).
  assert (C1024 : v_cap (u_cstk g) <= 1024) by (rewrite DC in LEc; lia).
  assert (V1024 : v_cap (u_vstk g) <= 1024) by (rewrite DV in LEv; lia).
  rewrite DC, DV.
  assert (VC2 : v_cap (u_vstk g) = v_cap (u_cstk g) \/ v_cap (u_vstk g) = 2 * v_cap (u_cstk g)) by (clear - TIE; lia).
  destruct (pairs_complete _ _ (cap32_le1024 _ CC C1024) VC2 V1024) as (p & INP & E1 & E2).
  exists p. split; [exact INP|]. rewrite E1, E2. split; reflexivity.
Qed.

Theorem gcapb2_sound : contract_sound segs OPS MP PB gcapb2_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gcapb2_contract c_apply] in HA. unfold gcapb2_apply in HA.
  pose proof (so_zero _ _ _ _ _ _ HS) as Pz. pose proof (so_facts _ _ _ _ _ _ HS) as Pfacts.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1%uint63 || PrimInt63.eqb mdi 2%uint63) eqn:EMD; [|discriminate].
  assert (MD : mdi = 1%uint63 \/ mdi = 2%uint63) by (apply orb_prop in EMD as [M|M]; apply Uint63.eqb_correct in M; [left| right]; exact M).
  destruct (GCap.carg ca 1%nat) as [|kC oc| | | | | | | | |] eqn:EC; try discriminate.
  destruct (GCap.carg ca 4%nat) as [|kV ov| | | | | | | | |] eqn:EV; try discriminate.
  cbv zeta in HA.
  match type of HA with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection HA as <-.
  apply andb_prop in COND as [COND NWv]. apply andb_prop in COND as [COND IMPv]. apply andb_prop in COND as [COND NWc].
  apply andb_prop in COND as [COND IMPc]. apply andb_prop in COND as [OC OV].
  pose proof (implied_sound E (s_facts st) _ Pz Pfacts IMPc) as Ic. pose proof (implied_sound E (s_facts st) _ Pz Pfacts IMPv) as Iv. cbn [fact_holds] in Ic, Iv.
  destruct (nowrap_kb_sound E (s_facts st) Pfacts kC BOUNDw NWc) as [_ DVc]. destruct (nowrap_kb_sound E (s_facts st) Pfacts kV BOUNDw NWv) as [_ DVv].
  rewrite DVc in Ic. rewrite DVv in Iv.
  destruct (split2 E st ms model mdi aw ws ca kC oc kV ov HS TO MD EC OC EV OV Ic Iv) as (p & INP & DCAPc & DCAPv).
  apply (Hk (post2 st kC (GCap.carg ca 3%nat) kV (GCap.carg ca 6%nat) p) (in_map _ _ _ INP) E ms model (env_ext_refl _ E) HMP).
  - unfold post2. apply (GCap.post_sound segs OPS MP E _ ms model kV _ (snd p)); [| exact DCAPv].
    exact (GCap.post_sound segs OPS MP E st ms model kC _ (fst p) HS DCAPc).
Qed.

End Sound.
End Pair.
End GCapB.
End TwinB.
