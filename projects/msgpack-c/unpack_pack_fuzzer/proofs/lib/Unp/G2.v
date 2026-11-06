(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Cost Acct.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Pot GPot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Ops GLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module G2.

Definition slot_win (kS : int) : sv * sv * sv := (VP kS wzero, VL (wlit 24%uint63), VL (wlit 4%uint63)).

Definition wins_shape (kS : int) (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match kind_of w with
                    | Some kd => if kd =? K_SLOT then win3_eqb w (slot_win kS) else true
                    | None => false
                    end) ws
  && existsb (win3_eqb (slot_win kS)) ws.

Definition litZ (v : sv) : option Z := match v with VL x => Some (w2Z x) | _ => None end.

Definition int_tag (v : sv) : bool :=
  match v with
  | VAlu ALU_ADD (VAlu ALU_SLT _ (VL z)) (VL two) => weqb z wzero && weqb two (wlit 2%uint63)
  | VAlu ALU_ADD (VL two) (VAlu ALU_SLT _ (VL z)) => weqb z wzero && weqb two (wlit 2%uint63)

  | VAlu ALU_XOR (VAluw ALU_SRL _ (VL s)) (VL three) => weqb s (wlit 31%uint63) && weqb three (wlit 3%uint63)
  | VAlu ALU_XOR (VL three) (VAluw ALU_SRL _ (VL s)) => weqb s (wlit 31%uint63) && weqb three (wlit 3%uint63)

  | VAlu ALU_XOR (VAlu ALU_SRL _ (VL s)) (VL three) => weqb s (wlit 63%uint63) && weqb three (wlit 3%uint63)
  | VAlu ALU_XOR (VL three) (VAlu ALU_SRL _ (VL s)) => weqb s (wlit 63%uint63) && weqb three (wlit 3%uint63)
  | _ => false
  end.

Lemma srl63_01 : forall E x s, weqb s (wlit 63%uint63) = true ->
  bv_unsigned (den E (VAlu ALU_SRL x (VL s))) = 0 \/ bv_unsigned (den E (VAlu ALU_SRL x (VL s))) = 1.
Proof.
  intros E x s Hs. apply (proj1 (weqb_ok _ _)) in Hs. subst s.
  change (den E (VAlu ALU_SRL x (VL (wlit 63)))) with (alu64 ALU_SRL (den E x) (den E (VL (wlit 63)))).
  cbn [alu64 alu]. change (den E (VL (wlit 63))) with (wbv (wlit 63)). rewrite bv_shiftr_unsigned, shamt6_bv.
  change (to_Z (shamt6 (wlit 63))) with 63.
  pose proof (bv_unsigned_in_range 64 (den E x)) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  rewrite Z.shiftr_div_pow2 by lia.
  destruct (Z_lt_le_dec (bv_unsigned (den E x)) (2 ^ 63)).
  - left. apply Z.div_small. lia.
  - right. symmetry. apply (Z.div_unique_pos _ _ 1 (bv_unsigned (den E x) - 2 ^ 63)); lia.
Qed.

Lemma srlw31_01 : forall E x s, weqb s (wlit 31%uint63) = true ->
  bv_unsigned (den E (VAluw ALU_SRL x (VL s))) = 0 \/ bv_unsigned (den E (VAluw ALU_SRL x (VL s))) = 1.
Proof.
  intros E x s Hs. apply (proj1 (weqb_ok _ _)) in Hs. subst s.
  cbn [den]. rewrite sext32_unsigned. unfold alu32, alu. rewrite bv_shiftr_unsigned, bv_and_unsigned, Z_to_bv_unsigned.
  change (den E (VL (wlit 31))) with (wbv (wlit 31)). rewrite low32_unsigned.
  change (Z.land (to_Z (lo32 (wlit 31))) (bv_wrap 32 31)) with 31.
  pose proof (bv_unsigned_in_range 32 (low32 (den E x))) as R. change (bv_modulus 32) with (2 ^ 32) in R.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (H : bv_unsigned (low32 (den E x)) / 2 ^ 31 = 0 \/ bv_unsigned (low32 (den E x)) / 2 ^ 31 = 1).
  { destruct (Z_lt_le_dec (bv_unsigned (low32 (den E x))) (2 ^ 31)).
    - left. apply Z.div_small. lia.
    - right. symmetry. apply (Z.div_unique_pos _ _ 1 (bv_unsigned (low32 (den E x)) - 2 ^ 31)); lia. }
  unfold sx32Z. destruct H as [H|H]; rewrite H; cbn; auto.
Qed.

Lemma xor3_tag : forall E a t, weqb t (wlit 3%uint63) = true ->
  (bv_unsigned (den E a) = 0 \/ bv_unsigned (den E a) = 1) ->
  (bv_unsigned (den E (VAlu ALU_XOR a (VL t))) = T_POSINT \/ bv_unsigned (den E (VAlu ALU_XOR a (VL t))) = T_NEGINT)
  /\ (bv_unsigned (den E (VAlu ALU_XOR (VL t) a)) = T_POSINT \/ bv_unsigned (den E (VAlu ALU_XOR (VL t) a)) = T_NEGINT).
Proof.
  intros E a t Ht H. apply (proj1 (weqb_ok _ _)) in Ht. subst t.
  change (den E (VAlu ALU_XOR a (VL (wlit 3)))) with (alu64 ALU_XOR (den E a) (den E (VL (wlit 3)))).
  change (den E (VAlu ALU_XOR (VL (wlit 3)) a)) with (alu64 ALU_XOR (den E (VL (wlit 3))) (den E a)).
  cbn [alu64 alu]. rewrite !bv_xor_unsigned. change (bv_unsigned (den E (VL (wlit 3)))) with 3.
  destruct H as [H|H]; rewrite H; split; (left; reflexivity) || (right; reflexivity).
Qed.

Lemma int_tag_sound : forall E v, int_tag v = true -> bv_unsigned (den E v) = T_POSINT \/ bv_unsigned (den E v) = T_NEGINT.
Proof.
  intros E v H. unfold int_tag in H.
  assert (SLT : forall a b, bv_unsigned (den E (VAlu ALU_SLT a b)) = 0 \/ bv_unsigned (den E (VAlu ALU_SLT a b)) = 1).
  { intros a b. cbn [den alu64 alu]. destruct (bv_lts (den E a) (den E b)); [right| left]; reflexivity. }
  destruct v as [| |op a b| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  {
  destruct a as [two| |opa x y| | | | | | | |]; try discriminate H.
  - destruct b as [| |opb x y| | | | | | | |]; try discriminate H. destruct opb; try discriminate H. destruct y as [z| | | | | | | | | |]; try discriminate H.
    apply andb_prop in H as [Z0 T2]. apply (proj1 (weqb_ok _ _)) in Z0. apply (proj1 (weqb_ok _ _)) in T2. subst z two.
    change (den E (VAlu ALU_ADD (VL (wlit 2)) (VAlu ALU_SLT x (VL wzero)))) with (alu64 ALU_ADD (den E (VL (wlit 2))) (den E (VAlu ALU_SLT x (VL wzero)))).
    cbn [alu64 alu]. rewrite bv_add_unsigned. change (bv_unsigned (den E (VL (wlit 2)))) with 2.
    destruct (SLT x (VL wzero)) as [X|X]; rewrite X; [left| right]; reflexivity.
  - destruct opa; try discriminate H. destruct y as [z| | | | | | | | | |]; try discriminate H. destruct b as [two| | | | | | | | | |]; try discriminate H.
    apply andb_prop in H as [Z0 T2]. apply (proj1 (weqb_ok _ _)) in Z0. apply (proj1 (weqb_ok _ _)) in T2. subst z two.
    change (den E (VAlu ALU_ADD (VAlu ALU_SLT x (VL wzero)) (VL (wlit 2)))) with (alu64 ALU_ADD (den E (VAlu ALU_SLT x (VL wzero))) (den E (VL (wlit 2)))).
    cbn [alu64 alu]. rewrite bv_add_unsigned. change (bv_unsigned (den E (VL (wlit 2)))) with 2.
    destruct (SLT x (VL wzero)) as [X|X]; rewrite X; [left| right]; reflexivity. }

  destruct a as [three| |opa x y|opa x y| | | | | | |]; try discriminate H.
  - destruct b as [| |opb x y|opb x y| | | | | | |]; try discriminate H.
    + destruct opb; try discriminate H. destruct y as [s| | | | | | | | | |]; try discriminate H.
      apply andb_prop in H as [S63 T3]. exact (proj2 (xor3_tag E _ three T3 (srl63_01 E x s S63))).
    + destruct opb; try discriminate H. destruct y as [s| | | | | | | | | |]; try discriminate H.
      apply andb_prop in H as [S31 T3]. exact (proj2 (xor3_tag E _ three T3 (srlw31_01 E x s S31))).
  - destruct opa; try discriminate H. destruct y as [s| | | | | | | | | |]; try discriminate H. destruct b as [three| | | | | | | | | |]; try discriminate H.
    apply andb_prop in H as [S63 T3]. exact (proj1 (xor3_tag E _ three T3 (srl63_01 E x s S63))).
  - destruct opa; try discriminate H. destruct y as [s| | | | | | | | | |]; try discriminate H. destruct b as [three| | | | | | | | | |]; try discriminate H.
    apply andb_prop in H as [S31 T3]. exact (proj1 (xor3_tag E _ three T3 (srlw31_01 E x s S31))).
Qed.

Definition complete_item (r : region) : bool :=
  PrimInt63.eqb (rg_lo r) 0%uint63 && sv_eqb (rg_hi r) (VL (wlit 24%uint63)) && rg_w r &&
  match cell_at r 0 4%uint63 with
  | Some tv =>
      match litZ tv with
      | Some t =>
          if t =? T_NIL then true
          else if t =? T_BOOLEAN then
            match cell_at r 8 1%uint63 with
            | Some bv => match litZ bv with Some b => (b =? 0) || (b =? 1) | None => false end
            | None => false
            end
          else if (t =? T_POSINT) || (t =? T_NEGINT) || (t =? T_FLOAT64) || (t =? T_FLOAT32) then
            match cell_at r 8 8%uint63 with Some _ => true | None => false end
          else if (t =? T_ARRAY) || (t =? T_MAP) || (t =? T_STR) || (t =? T_BIN) then
            match cell_at r 8 4%uint63, cell_at r 16 8%uint63 with
            | Some nv, Some pv => match litZ nv, litZ pv with Some n, Some p => (n =? 0) && (p =? 0) | _, _ => false end
            | _, _ => false
            end
          else false
      | None =>
          int_tag tv && match cell_at r 8 8%uint63 with Some _ => true | None => false end
      end
  | None => false
  end.

Section WithPc.
Variable CONSUME_PC : int.

Definition g2_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 then
      match ca with
      | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
          match slot with
          | VP kS os =>
              if weqb os wzero && negb (PrimInt63.eqb kS 0%uint63) && wins_shape kS ws
                 && match decide_ltu (s_facts st) cb ce with Some true => true | _ => false end
              then
                match IMap.find kS (s_regs st) with
                | Some r =>
                    if complete_item r then
                      match GPot.GPot.pot_scan_c (s_facts st) aw ws with
                      | Some sc =>
                      let ws' := GPot.GPot.pot_lit sc GPot.GPot.D_ITEMw (List.filter (fun w => negb (win3_eqb w (slot_win kS))) ws) in
                      Some [surg st [kS] [] (mk_args 2%uint63 aw ws' ca) [] (s_next st)]
                      | None => None
                      end
                    else None
                | None => None
                end
              else None
          | _ => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Definition g2_contract : contract := Contract CONSUME_PC g2_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma slot_win_den : forall E kS, wden E (slot_win kS) = Win (bv_unsigned (ev E kS)) 24 K_SLOT.
Proof.
  intros E kS. unfold slot_win, wden. rewrite (den_VP0 E kS wzero (weqb_refl _)). cbn [den]. rewrite !wbv_unsigned, !wlit_ok. reflexivity.
Qed.

Lemma litZ_sound : forall E v z, litZ v = Some z -> bv_unsigned (den E v) = z /\ 0 <= z < two64.
Proof.
  intros E v z H. destruct v; try discriminate. cbn [litZ] in H. injection H as <-. cbn [den]. rewrite wbv_unsigned.
  split; [reflexivity| apply w2Z_range].
Qed.

Lemma complete_item_sound : forall priv E m kS r z ls,
  region_ok segs priv E m kS r -> PrimInt63.eqb kS 0%uint63 = false -> complete_item r = true ->
  let B := bv_unsigned (ev E kS) in
  loZ r = 0 /\ hiZ E r = 24 /\ rg_w r = true /\
  exists o, tree_at (bmem_of segs m) z B o /\ (forall c, In c (tl (obj_cells B o)) -> Inv.cell_ok z ls c) /\ obj_bodies o = [] /\
            Cost.obj_depth o = 1%nat /\
            Pot.Pot.pk10_tree o = 10.
Proof.
  intros priv E m kS r z ls RO K CI. unfold complete_item in CI.
  apply andb_prop in CI as [SH CI]. apply andb_prop in SH as [SH W]. apply andb_prop in SH as [LO HI].
  apply Uint63.eqb_correct in LO. apply sv_eqb_eq in HI.
  assert (HLO : loZ r = 0) by (unfold loZ, keyZ, Mem.keyZ; rewrite LO; reflexivity).
  assert (HHI : hiZ E r = 24) by (unfold hiZ; rewrite HI; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  cbv zeta. split; [exact HLO|]. split; [exact HHI|]. split; [exact W|].
  set (B := bv_unsigned (ev E kS)). set (bm := bmem_of segs m).
  assert (T62 : 0 < two62Z) by (unfold two62Z; lia).
  destruct (cell_at r 0 4%uint63) as [tv|] eqn:CT; [|discriminate].
  destruct (cell_at_u32 segs priv E m kS r 0 tv RO K ltac:(lia) ltac:(unfold two62Z; lia) CT) as (UT & _ & _).
  destruct (litZ tv) as [t|] eqn:LT.
  2:{
      apply andb_prop in CI as [IT CV8]. destruct (cell_at r 8 8%uint63) as [v|] eqn:CV; [|discriminate].
      destruct (cell_at_u64 segs priv E m kS r 8 v RO K ltac:(lia) ltac:(unfold two62Z; lia) CV) as (UV & _ & _). fold B bm in UV.
      rewrite Z.add_0_r in UT. fold B bm in UT.
      pose proof (bv_unsigned_in_range _ (den E v)) as RV. rewrite bv_modulus_64, two64_eq in RV.
      destruct (int_tag_sound E tv IT) as [TY|TY]; rewrite TY in UT;
        [change (T_POSINT mod 2 ^ 32) with T_POSINT in UT| change (T_NEGINT mod 2 ^ 32) with T_NEGINT in UT];
        destruct (just_int bm z ls B _ _ UT UV ltac:(auto) RV) as (o & A & C); exists o; (split; [exact A| split; [exact C|]]);
        destruct A as [OA _]; destruct o; cbn [obj_bodies Cost.obj_depth]; try (split; [reflexivity| split; reflexivity]); exfalso;
        apply (proj1 (obj_at_split _ _ _)) in OA as [HD _]; destruct HD as [HT _]; cbn [obj_type] in HT;
        unfold u32_at in HT, UT; rewrite UT in HT; injection HT as HT; try discriminate HT. }
  destruct (litZ_sound E tv t LT) as [TV TR]. rewrite TV, Z.add_0_r in UT. fold B bm in UT.
  destruct (Z.eqb_spec t T_NIL) as [->|N0].
  { rewrite Z.mod_small in UT by (unfold T_NIL; lia). exists ONil. destruct (just_nil bm z ls B UT) as [A C]. auto. }
  destruct (Z.eqb_spec t T_BOOLEAN) as [->|N1].
  { destruct (cell_at r 8 1%uint63) as [bv|] eqn:CB; [|discriminate]. destruct (litZ bv) as [b|] eqn:LB; [|discriminate].
    destruct (cell_at_u8 segs priv E m kS r 8 bv RO K ltac:(lia) ltac:(unfold two62Z; lia) CB) as (UB & _ & _).
    destruct (litZ_sound E bv b LB) as [BV BR]. rewrite BV in UB. fold B bm in UB.
    rewrite Z.mod_small in UT by (unfold T_BOOLEAN; lia).
    exists (OBool (b =? 1)). destruct (just_bool bm z ls B (b =? 1) UT) as [A C]; [|auto].
    rewrite Z.mod_small in UB by lia.
    apply orb_prop in CI as [Hb|Hb]; apply Z.eqb_eq in Hb; subst b;
      [change (if 0 =? 1 then 1 else 0) with 0| change (if 1 =? 1 then 1 else 0) with 1]; exact UB. }
  destruct ((t =? T_POSINT) || (t =? T_NEGINT) || (t =? T_FLOAT64) || (t =? T_FLOAT32)) eqn:C4.
  { destruct (cell_at r 8 8%uint63) as [v|] eqn:CV; [|discriminate].
    destruct (cell_at_u64 segs priv E m kS r 8 v RO K ltac:(lia) ltac:(unfold two62Z; lia) CV) as (UV & _ & _). fold B bm in UV.
    pose proof (bv_unsigned_in_range _ (den E v)) as RV. rewrite bv_modulus_64, two64_eq in RV.
    assert (T10 : 0 <= t <= 10) by (unfold T_POSINT, T_NEGINT, T_FLOAT64, T_FLOAT32 in C4; lia).
    rewrite Z.mod_small in UT by lia.
    apply orb_prop in C4 as [C4|C4]; [apply orb_prop in C4 as [C4|C4]; [apply orb_prop in C4 as [C4|C4]|]|]; apply Z.eqb_eq in C4; subst t.
    - exists (OPos (bv_unsigned (den E v))). destruct (just_pos bm z ls B _ UT UV RV) as [A C]. auto.
    - exists (ONeg (bv_unsigned (den E v) - 2 ^ 64)). destruct (just_negu bm z ls B _ UT UV RV) as [A C]. auto.
    - exists (OF64 (bv_unsigned (den E v))). destruct (just_f64 bm z ls B _ UT UV) as [A C]. auto.
    - exists (OF32 (bv_unsigned (den E v))). destruct (just_f32 bm z ls B _ UT UV) as [A C]. auto. }
  destruct ((t =? T_ARRAY) || (t =? T_MAP) || (t =? T_STR) || (t =? T_BIN)) eqn:C2; [|discriminate].
  destruct (cell_at r 8 4%uint63) as [nv|] eqn:CN; [|discriminate]. destruct (cell_at r 16 8%uint63) as [pv|] eqn:CP; [|discriminate].
  destruct (litZ nv) as [n|] eqn:LN; [|discriminate]. destruct (litZ pv) as [p|] eqn:LP; [|discriminate].
  apply andb_prop in CI as [N0' P0]. apply Z.eqb_eq in N0'. apply Z.eqb_eq in P0. subst n p.
  destruct (cell_at_u32 segs priv E m kS r 8 nv RO K ltac:(lia) ltac:(unfold two62Z; lia) CN) as (UN & _ & _).
  destruct (cell_at_u64 segs priv E m kS r 16 pv RO K ltac:(lia) ltac:(unfold two62Z; lia) CP) as (UP & _ & _).
  destruct (litZ_sound E nv 0 LN) as [NV _]. destruct (litZ_sound E pv 0 LP) as [PV _].
  rewrite NV in UN. rewrite PV in UP. fold B bm in UN. fold B bm in UP. change (0 mod 2 ^ 32) with 0 in UN.
  assert (T10 : 0 <= t <= 10) by (unfold T_ARRAY, T_MAP, T_STR, T_BIN in C2; lia). rewrite Z.mod_small in UT by lia.
  apply orb_prop in C2 as [C2|C2]; [apply orb_prop in C2 as [C2|C2]; [apply orb_prop in C2 as [C2|C2]|]|]; apply Z.eqb_eq in C2; subst t.
  - exists (OArr 0 []). destruct (just_empty_arr bm z ls B UT UN UP) as [A C]. auto.
  - exists (OMap 0 []). destruct (just_empty_map bm z ls B UT UN UP) as [A C]. auto.
  - exists (OStr 0 0). destruct (just_str bm z ls B 0 0 UT UN UP ltac:(unfold LIMIT; lia) ltac:(intros _; reflexivity) ltac:(intros X; exfalso; exact (X eq_refl))) as [A C]. auto.
  - exists (OBin 0 0). destruct (just_bin bm z ls B 0 0 UT UN UP ltac:(unfold LIMIT; lia) ltac:(intros _; reflexivity) ltac:(intros X; exfalso; exact (X eq_refl))) as [A C]. auto.
Qed.

Lemma g2_apply_sound : forall E st ms model st',
  st_ok segs OPS E st ms model -> g2_apply st = Some [st'] -> st_ok segs OPS E st' ms model.
Proof.
  intros E st ms model st' HS AP.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  unfold g2_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct slot as [|kS os| | | | | | | | |]; try discriminate.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  destruct (IMap.find kS (s_regs st)) as [r|] eqn:FR; [|discriminate].
  destruct (complete_item r) eqn:CI; [|discriminate].
  destruct (GPot.GPot.pot_scan_c (s_facts st) aw ws) as [sc|] eqn:SCAN; [|discriminate].
  pose proof (GPot.GPot.pot_scan_c_ok E (s_facts st) aw ws sc Pfacts SCAN) as SCOK.
  injection AP as <-.
  apply andb_prop in COND as [COND DLT]. apply andb_prop in COND as [COND WSH]. apply andb_prop in COND as [OS KS0].
  apply (proj1 (weqb_ok _ _)) in OS. subst os. apply negb_true_iff in KS0.
  destruct (decide_ltu (s_facts st) cb ce) as [[|]|] eqn:DL; try discriminate.
  apply andb_prop in WSH as [WALL WEX].

  destruct (the_op_sound E st 1%uint63 aw ws _ TO) as (o & OPS1 & OID & DEC & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC). rewrite DEC in DEC0. injection DEC0 as <- <- <- <-.
  change (to_Z 1%uint63) with 1 in HC.
  cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC.
  cbn [map decode_uc] in HC.
  destruct HC as (g & L & P & O & Wk & M & _ & AX & SE).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap, Lzp, Lzf, Lc0, LD.
  pose proof P as (VC & EC & SC & CC & VV & EV & SV' & CV & LV & DL' & LA & ZV).

  pose proof (decide_ltu_sound E (s_facts st) Pfacts _ _ _ DL) as LT. apply (proj1 (ltu_iff _ _ true)) in LT.
  rewrite <- Lcb, <- Lce in LT.
  assert (DPOS : 1 <= u_D g).
  { unfold v_end in LT. rewrite EC, SC in LT. unfold u_D in *. nia. }
  assert (NE : u_levels g <> []) by (unfold u_D in DPOS; destruct (u_levels g); [cbn in DPOS; lia| discriminate]).
  destruct (LD NE) as (Lslot & _ & _). cbn [c_slot] in Lslot.

  destruct (complete_item_sound _ E (ms_mem ms) kS r (u_zone g) (u_levels g) (Preg kS r FR) KS0 CI) as (HLO & HHI & HW & o0 & TREE & TLC & NOB & DEP1 & PK10).
  assert (SLOT : u_cur_slot g = bv_unsigned (ev E kS)).
  { rewrite Lslot. exact (den_VP0 E kS wzero (weqb_refl _)). }

  set (ws' := List.filter (fun w => negb (win3_eqb w (slot_win kS))) ws) in *.
  assert (SUB : forall w, In w ws' -> In w ws /\ w <> slot_win kS).
  { intros w Hw. apply filter_In in Hw as [Hw NS]. split; [exact Hw|]. intros ->.
    unfold win3_eqb, slot_win in NS. rewrite !sv_eqb_refl in NS. discriminate. }
  assert (LEN' : Z.of_nat (length (GPot.GPot.pot_lit sc GPot.GPot.D_ITEMw ws')) < two63).
  { rewrite GPot.GPot.pot_lit_length. pose proof (filter_length_le (fun w => negb (win3_eqb w (slot_win kS))) ws) as FL. subst ws'. lia. }
  assert (DITEM : 0 <= w2Z GPot.GPot.D_ITEMw <= 2 ^ 20) by (change (w2Z GPot.GPot.D_ITEMw) with 40; lia).
  pose proof (GPot.GPot.scan_oldb E ws sc SCOK) as OLDB. pose proof (GPot.GPot.lit_newb E ws sc GPot.GPot.D_ITEMw SCOK DITEM) as NEWB.

  apply (surgery_sound segs OPS E (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [kS] [] (mk_args 2%uint63 aw (GPot.GPot.pot_lit sc GPot.GPot.D_ITEMw ws') _) [] (s_next st)).
  -   intros k [<-|[]]. split; [exact KS0|]. exists r. auto.
  - constructor.
  - intros k r' [].
  - intros k r' [].
  - intros k r' a [].
  - intros k1 r1 k2 r2 a [].
  -
    rewrite (ho_holds _ _ _ _ _ HOPS).
    exists 2, (den E aw), (map (wden E) (GPot.GPot.pot_lit sc GPot.GPot.D_ITEMw ws')), (map (den E) [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; VP kS wzero; tD; restD; rootT; n1; P1; zh]), LB.
    split; [apply mk_args_sound; exact LEN'|].

    split; [apply (aw_keep segs IMGX AW _ _ (map (wden E) ws')); [| exact (GPot.GPot.wins_keep_pot_set E sc _ _ OLDB NEWB LB)];
            apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); apply (UOK.unp_wins_keep_map E 1 g LB ws ws' P O Wk);
            [intros x Hx; left; exact (proj1 (SUB x Hx))
            |intros x Hx; destruct (UOK.filter_old ws [] (fun w => negb (win3_eqb w (slot_win kS))) x Hx) as [H0|Q];
             [left; rewrite app_nil_r in H0; exact H0
             |right; left; apply negb_false_iff in Q; apply win3_eqb_eq in Q; subst x; apply UOK.kind_sub; vm_compute; reflexivity]]|]. split.
    + apply (GPot.GPot.windows_wf_pot_set E sc _ _ OLDB NEWB LB _ (aw_ceiling_small segs IMGX AW model)).
      unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
      exact (proj1 (Forall_forall _ _) WF (wden E x) (in_map _ _ _ (proj1 (SUB x Hx)))).
    + cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. cbn [map decode_uc].
      exists g. split; [exact L| split; [exact P| split; [exact O| split; [| split; [exact M| split; [| split; [split; [exact (proj1 AX)| intros X; discriminate X]|]]]]]]].
      *
        apply GPot.GPot.wins_ok_pot_set.
        unfold wins_ok in *. apply Forall_forall. intros w Hw NS.
        apply in_map_iff in Hw as (x & <- & Hx). destruct (SUB x Hx) as [Hx0 NSx].
        pose proof (proj1 (forallb_forall _ _) WALL x Hx0) as OKx. cbn beta in OKx.
        destruct (kind_of x) as [kd|] eqn:KD; [|discriminate].
        pose proof (kind_of_sound E x kd KD) as WK.
        destruct (proj1 (Forall_forall _ _) Wk (wden E x) (in_map _ _ _ Hx0) NS) as [D1|[NB SO]]; [left; exact D1| right].
        split; [exact NB|].
        unfold sub_ok in SO |- *. cbv zeta in SO |- *.
        destruct SO as [A|[A|[(KK & lD & HlD & I2 & I3)|A]]]; [left; exact A| right; left; exact A| | right; right; right; exact A].
        exfalso. rewrite WK in KK. rewrite KK in OKx. change (K_SLOT =? K_SLOT) with true in OKx.
        apply win3_eqb_eq in OKx. exact (NSx OKx).
      *
        intros _. cbv zeta. exists o0. rewrite SLOT. destruct TREE as [OA TW].
        apply (proj1 (obj_at_split _ _ _)) in OA as [HD KA].
        split; [exact TW|]. split; [exact KA|]. split; [intros _; exact HD|]. split; [intros X; exact (False_ind _ (NE X))|].
        split; [exact TLC|]. split; [unfold bodies_ok; rewrite NOB; constructor|].
        split; [rewrite DEP1; pose proof (Acct.u_D_length g DL') as UDL; lia|].

        destruct (proj2 AX eq_refl) as (S0 & KP0 & PA0). exists S0. split; [exact KP0|].
        apply (GPot.GPot.pot_at_set E ws ws' sc _ _ SCOK); [intros x Hx; left; exact (proj1 (SUB x Hx))|].
        pose proof (GPot.GPot.lit_value E ws sc GPot.GPot.D_ITEMw _ SCOK PA0 DITEM) as LV0. destruct sc as [lo|]; [| exact I].
        rewrite LV0, (Pot.Pot.pot_val_item (u_levels g) S0 (Pot.Pot.pk10_tree o0)), PK10. reflexivity.
      *
        apply GPot.GPot.seal_ok_pot_set.
        apply (Seal.seal_ok_ws _ _ _ SE). intros w Hw _. apply in_map_iff in Hw as (x & <- & Hx). exact (in_map _ _ _ (proj1 (SUB x Hx))).
  -
    intros a FPa. split; [| intros k r' []].
    unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 2 _ (map (wden E) (GPot.GPot.pot_lit sc GPot.GPot.D_ITEMw ws')) _ a (mk_args_sound E 2%uint63 aw _ _ LEN'))) in FPa as (RA & NI & NW).
    assert (NW' : ~ in_ws (map (wden E) ws') a) by (intros X; apply NW; apply GPot.GPot.in_ws_pot_set; exact X). clear NW. rename NW' into NW.
    destruct (in_ws_dec (map (wden E) ws) a) as [IN|NIN].
    + right. exists kS, r. split; [left; reflexivity|]. split; [exact FR|].
      apply in_ws_map_iff in IN as (x & Hx & Ha).
      destruct (win3_eqb x (slot_win kS)) eqn:ISW.
      * apply win3_eqb_eq in ISW. subst x. rewrite slot_win_den in Ha. unfold in_iv, w_iv in Ha. cbn [w_lo w_len fst snd] in Ha.
        unfold inR. rewrite HLO, HHI. lia.
      * exfalso. apply NW. apply in_ws_map_iff. exists x. split; [|exact Ha]. apply filter_In. split; [exact Hx|]. rewrite ISW. reflexivity.
    + left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS).
      apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E) ws) _ a DEC)). auto.
  - constructor.
Qed.

Theorem g2_sound : contract_sound segs OPS MP PB g2_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [g2_contract c_apply] in HA.
  destruct (g2_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  - exfalso. unfold g2_apply in AP.
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
  - injection HA as <-.
    apply (Hk st' (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP).
    exact (g2_apply_sound E st ms model st' HS AP).
  - exfalso. unfold g2_apply in AP.
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End WithPc.
End G2.
