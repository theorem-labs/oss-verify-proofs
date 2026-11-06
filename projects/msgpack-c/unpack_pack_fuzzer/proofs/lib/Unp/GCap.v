(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GCap.

Definition cap_var (kB : int) (cap : sv) : option int :=
  match cap with
  | VAlu ALU_ADD (VP k1 o1) (VP k2 o2) =>
      if weqb o1 wzero && weqb o2 wzero then
        (if PrimInt63.eqb k1 kB then Some k2 else if PrimInt63.eqb k2 kB then Some k1 else None)
      else None
  | _ => None
  end.

Definition post (st : sstate) (kB : int) (cap : sv) (L : int) : sstate :=
  let st1 := addfact st (FEq cap (VP kB (wlit L))) in
  match cap_var kB cap with
  | Some x => addfact st1 (FEq (VP x wzero) (VL (wlit L)))
  | None => st1
  end.

Definition carg (ca : list sv) (i : nat) : sv := nth i ca (VL wzero).

Section Generic.
Variable CAP_PC : int.
Variable MD : int.
Variable ib ie ic : nat.
Variable CAPS : list int.
Variable PRE : sstate -> list sv -> bool.

Definition cap_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md MD then
        match carg ca ib with
        | VP kB ob =>
            let fs := s_facts st in let e := carg ca ie in let cap := carg ca ic in
            if weqb ob wzero && implied fs (FULe e cap) && implied fs (FULe cap e) && PRE st ca
            then Some (map (post st kB cap) CAPS)
            else None
        | _ => None
        end
      else None
  | None => None
  end.

Definition cap_contract : contract := Contract CAP_PC cap_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis SPLIT : forall E st ms model aw ws ca kB ob,
  st_ok segs OPS E st ms model -> the_op st = Some (MD, aw, ws, ca) ->
  carg ca ib = VP kB ob -> weqb ob wzero = true -> PRE st ca = true ->
  bv_unsigned (den E (carg ca ie)) = bv_unsigned (den E (carg ca ic)) ->
  exists L, In L CAPS /\ bv_unsigned (den E (carg ca ic)) = bv_unsigned (ev E kB) + to_Z L.

Lemma mod_add_cancel : forall B X L, 0 <= B -> 0 <= X < two64 -> 0 <= L -> B + L < two64 -> (B + X) mod two64 = B + L -> X = L.
Proof.
  intros B X L HB HX HL HBL H. pose proof two64_eq as T. set (M := two64) in *. clearbody M.
  destruct (Z_lt_ge_dec (B + X) M) as [Lt|Ge].
  - rewrite Z.mod_small in H by lia. lia.
  - exfalso. assert (E : (B + X) mod M = B + X - M).
    { symmetry. apply (Z.mod_unique_pos _ _ 1); lia. }
    rewrite E in H. lia.
Qed.

Lemma post_sound : forall E st ms model kB cap L,
  st_ok segs OPS E st ms model ->
  bv_unsigned (den E cap) = bv_unsigned (ev E kB) + to_Z L ->
  st_ok segs OPS E (post st kB cap L) ms model.
Proof.
  intros E st ms model kB cap L HS DC. unfold post.
  pose proof (bv_unsigned_in_range _ (den E cap)) as RC. rewrite bv_modulus_64 in RC.
  pose proof (bv_unsigned_in_range _ (ev E kB)) as RB. rewrite bv_modulus_64 in RB.
  pose proof (to_Z_bounded L) as RL.
  assert (F1 : fact_holds E (FEq cap (VP kB (wlit L)))).
  { cbn [fact_holds]. apply bv_eq. rewrite den_VPu, wlit_ok, <- DC. symmetry. apply Z.mod_small. exact RC. }
  pose proof (addfact_sound segs OPS E st ms model _ HS F1) as HS1.
  destruct (cap_var kB cap) as [x|] eqn:CV; [|exact HS1].
  apply addfact_sound; [exact HS1|]. cbn [fact_holds]. apply bv_eq.
  rewrite (den_VP0 E x wzero (weqb_refl _)). cbn [den]. rewrite wbv_unsigned, wlit_ok.
  unfold cap_var in CV. destruct cap as [| |op a1 a2| | | | | | | |]; try discriminate. destruct op; try discriminate.
  destruct a1 as [|k1 o1| | | | | | | | |]; try discriminate. destruct a2 as [|k2 o2| | | | | | | | |]; try discriminate.
  destruct (weqb o1 wzero && weqb o2 wzero) eqn:OO; [|discriminate]. apply andb_prop in OO as [O1 O2].
  pose proof (bv_unsigned_in_range _ (ev E x)) as RX. rewrite bv_modulus_64 in RX.
  assert (DC' : (bv_unsigned (ev E k1) + bv_unsigned (ev E k2)) mod two64 = bv_unsigned (ev E kB) + to_Z L).
  { rewrite <- DC. change (den E (VAlu ALU_ADD (VP k1 o1) (VP k2 o2))) with (bv_add (den E (VP k1 o1)) (den E (VP k2 o2))).
    rewrite bv_add_unsigned, (den_VP0 E k1 o1 O1), (den_VP0 E k2 o2 O2). unfold bv_wrap. rewrite bv_modulus_64. reflexivity. }
  destruct (PrimInt63.eqb k1 kB) eqn:K1.
  - injection CV as <-. apply Uint63.eqb_correct in K1. subst k1.
    apply (mod_add_cancel (bv_unsigned (ev E kB)) _ (to_Z L)); lia.
  - destruct (PrimInt63.eqb k2 kB) eqn:K2; [|discriminate]. injection CV as <-. apply Uint63.eqb_correct in K2. subst k2.
    rewrite Z.add_comm in DC'.
    apply (mod_add_cancel (bv_unsigned (ev E kB)) _ (to_Z L)); lia.
Qed.

Lemma cap_apply_sound : forall E st ms model sts,
  st_ok segs OPS E st ms model -> cap_apply st = Some sts ->
  exists st', In st' sts /\ s_next st' = s_next st /\ st_ok segs OPS E st' ms model.
Proof.
  intros E st ms model sts HS AP.
  pose proof (so_zero _ _ _ _ _ _ HS) as Pz. pose proof (so_facts _ _ _ _ _ _ HS) as Pfacts.
  unfold cap_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi MD) eqn:EMD; [|discriminate]. apply Uint63.eqb_correct in EMD. subst mdi.
  destruct (carg ca ib) as [|kB ob| | | | | | | | |] eqn:EB; try discriminate.
  cbv zeta in AP.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection AP as <-.
  apply andb_prop in COND as [COND HPRE]. apply andb_prop in COND as [COND IMP2]. apply andb_prop in COND as [OB IMP1].
  pose proof (implied_sound E (s_facts st) _ Pz Pfacts IMP1) as I1. pose proof (implied_sound E (s_facts st) _ Pz Pfacts IMP2) as I2.
  cbn [fact_holds] in I1, I2.
  destruct (SPLIT E st ms model aw ws ca kB ob HS TO EB OB HPRE ltac:(lia)) as (L & INL & DCAP).
  exists (post st kB (carg ca ic) L). split; [apply in_map; exact INL|]. split.
  - unfold post. destruct (cap_var _ _); reflexivity.
  - apply post_sound; assumption.
Qed.

Theorem cap_sound : contract_sound segs OPS MP PB cap_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [cap_contract c_apply] in HA.
  destruct (cap_apply_sound E st ms model sts HS HA) as (st' & IN & NX & OK').
  exact (Hk st' IN E ms model (env_ext_refl (s_next st) E) HMP OK').
Qed.

End Sound.
End Generic.

Definition CAPS : list int := [256; 512; 1024; 2048; 4096]%uint63.

Lemma cap32_small : forall c, cap32_b c = true -> c <= 1001 -> c = 32 \/ c = 64 \/ c = 128 \/ c = 256 \/ c = 512.
Proof.
  intros c H LE. unfold cap32_b, EMBED_STACK in H. apply andb_prop in H as [H P2]. apply andb_prop in H as [GE MD].
  apply Z.leb_le in GE. apply Z.eqb_eq in MD. apply pow2_b_spec in P2 as (k & Hk & Hq).
  assert (C : c = 32 * 2 ^ k) by (rewrite <- Hq; pose proof (Z.div_mod c 32 ltac:(lia)); lia).
  assert (K5 : k < 5).
  { destruct (Z_lt_ge_dec k 5) as [|G]; [assumption|]. exfalso.
    pose proof (Z.pow_le_mono_r 2 5 k ltac:(lia) ltac:(lia)) as X. change (2 ^ 5) with 32 in X. lia. }
  assert (KK : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4) by lia.
  destruct KK as [->|[->|[->|[->| ->]]]]; subst c; [left| right; left| right; right; left| right; right; right; left| right; right; right; right];
    reflexivity.
Qed.

Section Unp.
Variable CAP_PC : int.
Variable isV : bool.

Definition IB : nat := if isV then 4%nat else 1%nat.
Definition IE : nat := if isV then 5%nat else 2%nat.
Definition IC : nat := if isV then 6%nat else 3%nat.

Definition gcap_contract : contract := cap_contract CAP_PC 1%uint63 IB IE IC CAPS (fun _ _ => true).

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma unp_split : forall E st ms model aw ws ca kB ob,
  st_ok segs OPS E st ms model -> the_op st = Some (1%uint63, aw, ws, ca) ->
  carg ca IB = VP kB ob -> weqb ob wzero = true -> true = true ->
  bv_unsigned (den E (carg ca IE)) = bv_unsigned (den E (carg ca IC)) ->
  exists L, In L CAPS /\ bv_unsigned (den E (carg ca IC)) = bv_unsigned (ev E kB) + to_Z L.
Proof.
  intros E st ms model aw ws ca kB ob HS TO EB OB _ EQ.
  pose proof (so_ops _ _ _ _ _ _ HS) as Pops.
  destruct (the_op_sound E st 1%uint63 aw ws _ TO) as (o & OPS1 & OID & DEC & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC). rewrite DEC in DEC0. injection DEC0 as <- <- <- <-.
  change (to_Z 1%uint63) with 1 in HC.
  cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC.
  destruct (decode_uc (map (den E) ca)) as [u|] eqn:DU; [|contradiction].
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate DU.
  cbn [map decode_uc] in DU. injection DU as <-.
  destruct HC as (g & L & P & O & Wk & M & _).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap, Lzp, Lzf, Lc0, LD.
  pose proof P as (VC & EC & SC & CC & VV & EV & SV' & CV & LV & DL' & LA & ZV).
  set (V := if isV then u_vstk g else u_cstk g).
  assert (VF : v_elt V = 8 /\ cap32_b (v_cap V) = true /\ v_size V <= 1001 /\
               v_begin V = bv_unsigned (den E (VP kB ob)) /\
               v_end V = bv_unsigned (den E (carg [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] IE)) /\
               v_capend V = bv_unsigned (den E (carg [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] IC))).
  { subst V. unfold LIMIT in DL'. unfold IB, IE, IC in *. destruct isV; cbn [carg nth] in EB |- *; rewrite <- EB.
    - repeat split; [exact EV| exact CV| lia| exact Lvb| exact Lve| exact Lvcap].
    - repeat split; [exact EC| exact CC| lia| exact Lcb| exact Lce| exact Lccap]. }
  destruct VF as (VELT & VCAP & VSZ & LVB & LVE & LVC).
  rewrite (den_VP0 E kB ob OB) in LVB.
  assert (SZC : v_size V = v_cap V).
  { unfold v_end, v_capend in LVE, LVC. rewrite VELT in LVE, LVC. lia. }
  rewrite SZC in VSZ.
  assert (DCAP : bv_unsigned (den E (carg [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] IC))
                 = bv_unsigned (ev E kB) + 8 * v_cap V).
  { rewrite <- LVC. unfold v_capend. rewrite VELT, LVB. reflexivity. }
  destruct (cap32_small _ VCAP VSZ) as [C|[C|[C|[C|C]]]]; rewrite C in DCAP.
  - exists 256%uint63. split; [cbn [CAPS In]; tauto| exact DCAP].
  - exists 512%uint63. split; [cbn [CAPS In]; tauto| exact DCAP].
  - exists 1024%uint63. split; [cbn [CAPS In]; tauto| exact DCAP].
  - exists 2048%uint63. split; [cbn [CAPS In]; tauto| exact DCAP].
  - exists 4096%uint63. split; [cbn [CAPS In]; tauto| exact DCAP].
Qed.

Theorem gcap_sound : contract_sound segs OPS MP PB gcap_contract.
Proof. exact (cap_sound CAP_PC 1%uint63 IB IE IC CAPS (fun _ _ => true) segs OPS MP PB unp_split). Qed.

End Sound.
End Unp.
End GCap.
