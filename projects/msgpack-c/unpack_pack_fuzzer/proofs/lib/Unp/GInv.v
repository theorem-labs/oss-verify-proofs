(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp GWin GCap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GInv.

Definition LO4096 : w64 := wlit 4096%uint63.
Definition W8 : w64 := wlit 8%uint63.
Definition W256 : w64 := wlit 256%uint63.

Definition top_anchor_facts (fs : list fact) (e : sv) : list fact :=
  match e with
  | VP k o =>
      if weqb o W8 && negb (PrimInt63.eqb k 0%uint63) then
        (if PrimInt63.leb 3%uint63 (find_align fs k) then [] else [FAlign k 3%uint63])
        ++ (match find_range fs k with Some _ => [] | None => [FRange k LO4096 GW.HMAX] end)
      else []
  | _ => []
  end.

Definition cap_facts (b cap : sv) : list fact :=
  match b with
  | VP kB ob =>
      if weqb ob wzero then
        match GCap.cap_var kB cap with
        | Some x => [FULe (VL W256) (VP x wzero); FULe (VP x wzero) (VL GW.HMAX)]
        | None => []
        end
      else []
  | _ => []
  end.

Definition base_facts (cb ce ccap vb ve vcap : sv) : list fact := [FULe cb ce; FULe ce ccap; FULt vb ve; FULe ve vcap].

Definition inv_facts (fs : list fact) (ca : list sv) : list fact :=
  match ca with
  | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
      let base := base_facts cb ce ccap vb ve vcap in
      let d1 := match decide_ltu (base ++ fs) cb ce with Some true => true | _ => false end in
      base
      ++ (if d1 then [FULt cb ce; FULt (VL wzero) P1] else [])
      ++ top_anchor_facts fs ve
      ++ (if d1 then top_anchor_facts fs ce else [])
      ++ cap_facts cb ccap ++ cap_facts vb vcap
  | _ => []
  end.

Definition fresh_facts (fs new : list fact) : list fact :=
  List.filter (fun f => negb (existsb (fact_eqb f) fs)) new.

Definition addfacts (st : sstate) (l : list fact) : sstate := fold_right (fun f s => addfact s f) st l.

Lemma addfacts_next : forall l st, s_next (addfacts st l) = s_next st.
Proof. induction l as [|f l IH]; intros st; [reflexivity|]. cbn [addfacts fold_right]. unfold addfact. cbn [s_next]. exact (IH st). Qed.

Section WithPc.
Variable INV_PC : int.

Definition ginv_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 || PrimInt63.eqb md 2%uint63
      then Some [addfacts st (fresh_facts (s_facts st) (inv_facts (s_facts st) ca))]
      else None
  | None => None
  end.

Definition ginv_contract : contract := Contract INV_PC ginv_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma addfacts_sound : forall E l st ms model,
  st_ok segs OPS E st ms model -> Forall (fact_holds E) l -> st_ok segs OPS E (addfacts st l) ms model.
Proof.
  intros E l. induction l as [|f l IH]; intros st ms model HS FH; [exact HS|].
  cbn [addfacts fold_right]. inversion FH as [|? ? Hf Hl]; subst.
  apply (addfact_sound segs OPS); [exact (IH st ms model HS Hl)| exact Hf].
Qed.

Record vfacts (B Ee C : Z) (sz cap : Z) : Prop := VF {
  vf_end : Ee = B + 8 * sz;
  vf_cap : C = B + 8 * cap;
  vf_sz : 0 <= sz <= cap;
  vf_lo : 4096 <= B;
  vf_hi : B + 8 * cap <= two62Z;
  vf_al : B mod 8 = 0;
  vf_c32 : 32 <= cap
}.

Lemma top_anchor_sound : forall E fs k o B Ee C sz cap,
  vfacts B Ee C sz cap -> 1 <= sz ->
  bv_unsigned (den E (VP k o)) = Ee ->
  Forall (fact_holds E) (top_anchor_facts fs (VP k o)).
Proof.
  intros E fs k o B Ee C sz cap V SZ DEN. unfold top_anchor_facts.
  destruct (weqb o W8 && negb (PrimInt63.eqb k 0%uint63)) eqn:C0; [|constructor].
  apply andb_prop in C0 as [O8 _]. apply weqb_eq in O8. subst o.
  destruct V as [VE VC VS VL VH VA _].
  pose proof two64_eq as T64. pose proof (evk_range E k) as RK.
  assert (W8v : w2Z W8 = 8) by (unfold W8; rewrite wlit_ok; reflexivity).
  rewrite den_VPu, W8v in DEN.
  assert (two62Z < two64) by (unfold two62Z; rewrite T64; lia).

  assert (EK : bv_unsigned (ev E k) = Ee - 8).
  { assert (R : 0 <= Ee - 8 < two64) by (unfold two62Z in *; lia).
    destruct (Z_lt_ge_dec (bv_unsigned (ev E k) + 8) two64) as [Lt|Ge].
    - rewrite Z.mod_small in DEN by lia. lia.
    - exfalso. assert (X : (bv_unsigned (ev E k) + 8) mod two64 = bv_unsigned (ev E k) + 8 - two64).
      { symmetry. apply (Z.mod_unique_pos _ _ 1); lia. }
      rewrite X in DEN. unfold two62Z in *. lia. }
  apply Forall_app. split.
  - destruct (PrimInt63.leb 3%uint63 (find_align fs k)); [constructor|]. constructor; [|constructor].
    cbn [fact_holds]. change (to_Z 3%uint63) with 3. change (2 ^ 3) with 8. rewrite EK, VE.
    replace (B + 8 * sz - 8) with (B + (sz - 1) * 8) by lia. rewrite Z.mod_add by lia. exact VA.
  - destruct (find_range fs k); [constructor|]. constructor; [|constructor].
    cbn [fact_holds]. rewrite GW.HMAX_val. unfold LO4096. rewrite wlit_ok. change (to_Z 4096%uint63) with 4096. rewrite EK. lia.
Qed.

Lemma cap_facts_sound : forall E b cap B Ee C sz cp,
  vfacts B Ee C sz cp ->
  bv_unsigned (den E b) = B -> bv_unsigned (den E cap) = C ->
  Forall (fact_holds E) (cap_facts b cap).
Proof.
  intros E b cap B Ee C sz cp V DB DC. unfold cap_facts.
  destruct b as [|kB ob| | | | | | | | |]; try constructor.
  destruct (weqb ob wzero) eqn:OB; [|constructor].
  destruct (GCap.cap_var kB cap) as [x|] eqn:CV; [|constructor].
  rewrite (den_VP0 E kB ob OB) in DB.
  destruct V as [VE VC VS VL VH VA V32].
  pose proof two64_eq as T64. pose proof (evk_range E x) as RX. pose proof (evk_range E kB) as RB.
  assert (H62 : two62Z < two64) by (unfold two62Z; rewrite T64; lia).

  assert (EX : bv_unsigned (ev E x) = 8 * cp).
  { unfold GCap.cap_var in CV. destruct cap as [| |op a1 a2| | | | | | | |]; try discriminate. destruct op; try discriminate.
    destruct a1 as [|k1 o1| | | | | | | | |]; try discriminate. destruct a2 as [|k2 o2| | | | | | | | |]; try discriminate.
    destruct (weqb o1 wzero && weqb o2 wzero) eqn:OO; [|discriminate]. apply andb_prop in OO as [O1 O2].
    assert (DC' : (bv_unsigned (ev E k1) + bv_unsigned (ev E k2)) mod two64 = B + 8 * cp).
    { rewrite <- VC, <- DC. change (den E (VAlu ALU_ADD (VP k1 o1) (VP k2 o2))) with (bv_add (den E (VP k1 o1)) (den E (VP k2 o2))).
      rewrite bv_add_unsigned, (den_VP0 E k1 o1 O1), (den_VP0 E k2 o2 O2). unfold bv_wrap. rewrite bv_modulus_64. reflexivity. }
    destruct (PrimInt63.eqb k1 kB) eqn:K1.
    - injection CV as <-. apply Uint63.eqb_correct in K1. subst k1. rewrite DB in DC'.
      apply (GCap.mod_add_cancel B _ (8 * cp)); lia.
    - destruct (PrimInt63.eqb k2 kB) eqn:K2; [|discriminate]. injection CV as <-. apply Uint63.eqb_correct in K2. subst k2.
      rewrite DB, Z.add_comm in DC'. apply (GCap.mod_add_cancel B _ (8 * cp)); lia. }
  constructor; [|constructor; [|constructor]].
  - cbn [fact_holds]. rewrite den_VL, (den_VP0 E x wzero (weqb_refl _)), EX. unfold W256. rewrite wlit_ok. change (to_Z 256%uint63) with 256. lia.
  - cbn [fact_holds]. rewrite den_VL, (den_VP0 E x wzero (weqb_refl _)), EX, GW.HMAX_val. lia.
Qed.

Lemma fresh_facts_sound : forall E fs new, Forall (fact_holds E) new -> Forall (fact_holds E) (fresh_facts fs new).
Proof.
  intros E fs new H. unfold fresh_facts. apply Forall_forall. intros f Hf. apply filter_In in Hf as [Hf _].
  exact (proj1 (Forall_forall _ _) H f Hf).
Qed.

Lemma inv_facts_sound : forall E st ms model md aw ws ca,
  st_ok segs OPS E st ms model -> the_op st = Some (md, aw, ws, ca) ->
  PrimInt63.eqb md 1%uint63 || PrimInt63.eqb md 2%uint63 = true ->
  Forall (fact_holds E) (inv_facts (s_facts st) ca).
Proof.
  intros E st ms model md aw ws ca HS TO MD.
  pose proof (so_ops _ _ _ _ _ _ HS) as Pops. pose proof (so_facts _ _ _ _ _ _ HS) as Pfacts.
  destruct (the_op_sound E st md aw ws _ TO) as (o & OPS1 & OID & DEC & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (mdZ & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC). rewrite DEC in DEC0. injection DEC0 as <- <- <- <-.
  unfold inv_facts.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try apply Forall_nil.
  assert (HC' : unp_client segs (to_Z md) (UC (bv_unsigned (den E root)) (bv_unsigned (den E cb)) (bv_unsigned (den E ce)) (bv_unsigned (den E ccap))
                   (bv_unsigned (den E vb)) (bv_unsigned (den E ve)) (bv_unsigned (den E vcap)) (bv_unsigned (den E zptr))
                   (bv_unsigned (den E zfree)) (bv_unsigned (den E c0)) (bv_unsigned (den E slot)) (bv_unsigned (den E tD))
                   (bv_unsigned (den E restD)) (bv_unsigned (den E rootT)) (bv_unsigned (den E n1)) (bv_unsigned (den E P1))) LB (map (wden E) ws) (ms_mem ms)).
  { cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [map decode_uc] in HC.
    apply orb_prop in MD as [M|M]; apply Uint63.eqb_correct in M; subst md.
    - change (to_Z 1%uint63) with 1 in HC |- *. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC. exact HC.
    - change (to_Z 2%uint63) with 2 in HC |- *. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC. exact HC. }
  clear HC. destruct HC' as (g & L & P & O & Wk & M & _).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lcb, Lce, Lccap, Lvb, Lve, Lvcap, LD.
  pose proof P as (VC & EC & SC & CC & VV & EV & SV' & CV & LV & DL' & LA & ZV).
  destruct O as [OIN _].

  assert (BLK : forall V, (V = u_cstk g \/ V = u_vstk g) -> v_elt V = 8 ->
            4096 <= v_begin V /\ v_begin V + 8 * v_cap V <= two62Z).
  { intros V HV EL.
    assert (IN : In (v_begin V, v_bytes V) LB).
    { apply OIN. unfold owned, cstk_block, vstk_block. destruct HV as [-> | ->]; cbn [In]; tauto. }
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA IN) as (B1 & B2 & B3 & B4 & _).
    pose proof (aw_blocks_lo segs IMGX AW _ LB _ (ms_mem ms) model _ HA IN) as B5.
    pose proof (aw_ceiling_small segs IMGX AW model) as B6.
    cbn [fst snd] in B1, B2, B3, B5. unfold v_bytes in B3. rewrite EL in B3. unfold two62Z in *. lia. }
  assert (C32 : forall c, cap32_b c = true -> 32 <= c).
  { intros c H. unfold cap32_b, EMBED_STACK in H. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply Z.leb_le in H. exact H. }
  pose proof (Zle_0_nat (length (u_levels g))) as D0. fold (u_D g) in D0.
  assert (VFC : vfacts (bv_unsigned (den E cb)) (bv_unsigned (den E ce)) (bv_unsigned (den E ccap)) (v_size (u_cstk g)) (v_cap (u_cstk g))).
  { destruct VC as (V1 & V2 & V3 & V4). destruct (BLK (u_cstk g) (or_introl eq_refl) EC) as [B1 B2].
    constructor.
    - rewrite <- Lcb, <- Lce. unfold v_end. rewrite EC. reflexivity.
    - rewrite <- Lcb, <- Lccap. unfold v_capend. rewrite EC. reflexivity.
    - exact V2.
    - rewrite <- Lcb. exact B1.
    - rewrite <- Lcb. exact B2.
    - rewrite <- Lcb. exact V4.
    - exact (C32 _ CC). }
  assert (VFV : vfacts (bv_unsigned (den E vb)) (bv_unsigned (den E ve)) (bv_unsigned (den E vcap)) (v_size (u_vstk g)) (v_cap (u_vstk g))).
  { destruct VV as (V1 & V2 & V3 & V4). destruct (BLK (u_vstk g) (or_intror eq_refl) EV) as [B1 B2].
    constructor.
    - rewrite <- Lvb, <- Lve. unfold v_end. rewrite EV. reflexivity.
    - rewrite <- Lvb, <- Lvcap. unfold v_capend. rewrite EV. reflexivity.
    - exact V2.
    - rewrite <- Lvb. exact B1.
    - rewrite <- Lvb. exact B2.
    - rewrite <- Lvb. exact V4.
    - exact (C32 _ CV). }

  assert (BASE : Forall (fact_holds E) (base_facts cb ce ccap vb ve vcap)).
  { destruct VFC as [CE1 CC1 CS1 _ _ _ _]. destruct VFV as [VE1 VC1 VS1 _ _ _ _].
    unfold base_facts. repeat constructor; cbn [fact_holds]; lia. }
  cbv zeta.
  apply Forall_app. split; [exact BASE|].

  assert (D1 : (match decide_ltu (base_facts cb ce ccap vb ve vcap ++ s_facts st) cb ce with Some true => true | _ => false end) = true ->
               bv_unsigned (den E cb) < bv_unsigned (den E ce)).
  { intros H. destruct (decide_ltu _ cb ce) as [[|]|] eqn:DL; try discriminate.
    assert (FH : facts_hold E (base_facts cb ce ccap vb ve vcap ++ s_facts st)) by (apply Forall_app; split; assumption).
    pose proof (decide_ltu_sound E _ FH _ _ _ DL) as X. apply (proj1 (ltu_iff _ _ true)) in X. exact X. }
  apply Forall_app. split.
  { destruct (match decide_ltu _ cb ce with Some true => true | _ => false end) eqn:DD; [|constructor].
    specialize (D1 eq_refl). constructor; [exact D1|]. constructor; [|constructor].

    cbn [fact_holds]. rewrite den_VL, wzero_ok.
    destruct VFC as [CE1 _ _ _ _ _ _].
    assert (NE : u_levels g <> []).
    { intros EQ. unfold u_D in SC. rewrite EQ in SC. cbn [length Z.of_nat] in SC. lia. }
    destruct (LD NE) as (_ & _ & (l1 & ls1 & EL & _ & _ & LP)).
    assert (LV1 : level_valid l1) by (apply (proj1 (Forall_forall _ _) LV); rewrite EL; left; reflexivity).
    destruct LV1 as (_ & _ & _ & NZ & _). rewrite LP in NZ.
    pose proof (bv_unsigned_in_range _ (den E P1)) as R. lia. }
  apply Forall_app. split.
  { destruct ve as [|kv ov| | | | | | | | |]; try constructor.
    apply (top_anchor_sound E (s_facts st) kv ov _ _ _ _ _ VFV); [lia| reflexivity]. }
  apply Forall_app. split.
  { destruct (match decide_ltu _ cb ce with Some true => true | _ => false end) eqn:DD; [|constructor].
    specialize (D1 eq_refl).
    destruct ce as [|kc oc| | | | | | | | |]; try constructor.
    apply (top_anchor_sound E (s_facts st) kc oc _ _ _ _ _ VFC); [|reflexivity].
    destruct VFC as [CE1 _ _ _ _ _ _]. lia. }
  apply Forall_app. split.
  - exact (cap_facts_sound E cb ccap _ _ _ _ _ VFC eq_refl eq_refl).
  - exact (cap_facts_sound E vb vcap _ _ _ _ _ VFV eq_refl eq_refl).
Qed.

Theorem ginv_sound : contract_sound segs OPS MP PB ginv_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [ginv_contract c_apply] in HA. unfold ginv_apply in HA.
  destruct (the_op st) as [[[[md aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb md 1%uint63 || PrimInt63.eqb md 2%uint63) eqn:MD; [|discriminate].
  injection HA as <-.
  set (st' := addfacts st (fresh_facts (s_facts st) (inv_facts (s_facts st) ca))).
  assert (OK' : st_ok segs OPS E st' ms model).
  { apply addfacts_sound; [exact HS|]. apply fresh_facts_sound. exact (inv_facts_sound E st ms model md aw ws ca HS TO MD). }
  exact (Hk st' (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP OK').
Qed.

End Sound.
End WithPc.
End GInv.
