(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Cost Acct.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Pot GPot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp G3 GWin G2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 GW.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module G2Z.

Definition complete_item_at (r : region) (b : Z) : option sv :=
  match cell_at r b 4%uint63 with
  | Some tv =>
      match G2.litZ tv with
      | Some t =>
          if t =? T_NIL then Some tv
          else if t =? T_BOOLEAN then
            match cell_at r (b + 8) 1%uint63 with
            | Some bv => match G2.litZ bv with Some x => if (x =? 0) || (x =? 1) then Some tv else None | None => None end
            | None => None
            end
          else if (t =? T_POSINT) || (t =? T_NEGINT) || (t =? T_FLOAT64) || (t =? T_FLOAT32) then
            match cell_at r (b + 8) 8%uint63 with Some _ => Some tv | None => None end
          else if (t =? T_ARRAY) || (t =? T_MAP) || (t =? T_STR) || (t =? T_BIN) then
            match cell_at r (b + 8) 4%uint63, cell_at r (b + 16) 8%uint63 with
            | Some nv, Some pv => match G2.litZ nv, G2.litZ pv with Some n, Some p => if (n =? 0) && (p =? 0) then Some tv else None | _, _ => None end
            | _, _ => None
            end
          else None
      | None => if G2.int_tag tv then match cell_at r (b + 8) 8%uint63 with Some _ => Some tv | None => None end else None
      end
  | None => None
  end.

Section WithPc.
Variable CONSUME_PC : int.

Definition g2z_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 then
      match ca with
      | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
          match root with
          | VP k1 oR =>
              match okey oR, IMap.find k1 (s_regs st) with
              | Some key, Some r1 =>
                  if sv_eqb cb ce && negb (PrimInt63.eqb k1 0%uint63) && only_kind 4 None ws
                     && Z.ltb (keyZ key + 24) two62Z && Z.ltb (Z.of_nat (length ws)) 4096
                  then match complete_item_at r1 (keyZ key) with
                       | Some tsv =>
                           match GPot.GPot.pot_scan_c (s_facts st) aw ws with
                           | Some sc =>
                           let post (rt : sv) (nf : list fact) :=
                             surg st [] [] (mk_args 2%uint63 aw (GPot.GPot.pot_lit sc GPot.GPot.D_ITEMw ws)
                                                    [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD;
                                                                   rt; VL wzero; VL wzero; zh]) nf (s_next st) in

                           if G2.int_tag tsv
                           then Some [post (VL (wlit 2%uint63)) [FEq tsv (VL (wlit 2%uint63))]; post (VL (wlit 3%uint63)) [FEq tsv (VL (wlit 3%uint63))]]
                           else Some [post tsv []]
                           | None => None
                           end
                       | None => None
                       end
                  else None
              | _, _ => None
              end
          | _ => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Definition g2z_contract : contract := Contract CONSUME_PC g2z_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Ltac fin A C := split; [exact A| split; [exact C| split; [reflexivity| split; [reflexivity| split; [reflexivity| split; [reflexivity| split; [cbn; exact I| split; reflexivity]]]]]]].

Lemma complete_item_at_sound : forall priv E m k r b tsv z ls,
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> - two62Z <= b -> b + 24 < two62Z ->
  complete_item_at r b = Some tsv ->
  let B := bv_unsigned (ev E k) + b in
  let t := bv_unsigned (den E tsv) in
  0 <= t <= 10 /\
  exists o, tree_at (bmem_of segs m) z B o /\ (forall c, In c (tl (obj_cells B o)) -> Inv.cell_ok z ls c) /\ obj_bodies o = [] /\
            obj_type o = t /\ obj_cnt o = 0 /\ obj_ptr o = 0 /\ kids_at (bmem_of segs m) o /\
            Cost.obj_depth o = 1%nat /\
            Pot.Pot.pk10_tree o = 10.
Proof.
  intros priv E m k r b tsv z ls RO K Hb1 Hb2 CI. unfold complete_item_at in CI. cbv zeta.
  set (B := bv_unsigned (ev E k) + b). set (bm := bmem_of segs m).
  destruct (cell_at r b 4%uint63) as [tv|] eqn:CT; [|discriminate].
  destruct (cell_at_u32_s segs priv E m k r b tv RO K ltac:(lia) ltac:(lia) CT) as (UT & _ & _).
  destruct (G2.litZ tv) as [t0|] eqn:LT.
  2:{
      destruct (G2.int_tag tv) eqn:IT; [|discriminate]. destruct (cell_at r (b + 8) 8%uint63) as [v|] eqn:CV; [|discriminate]. injection CI as <-.
      destruct (cell_at_u64_s segs priv E m k r (b + 8) v RO K ltac:(lia) ltac:(lia) CV) as (UV & _ & _).
      replace (bv_unsigned (ev E k) + (b + 8)) with (B + 8) in UV by (subst B; lia). fold bm in UV. fold B bm in UT.
      pose proof (bv_unsigned_in_range _ (den E v)) as RV. rewrite bv_modulus_64, two64_eq in RV.
      destruct (G2.int_tag_sound E tv IT) as [TY|TY]; rewrite TY in UT |- *;
        [change (T_POSINT mod 2 ^ 32) with T_POSINT in UT| change (T_NEGINT mod 2 ^ 32) with T_NEGINT in UT];
        (split; [unfold T_POSINT, T_NEGINT; lia|]).
      - exists (OPos (bv_unsigned (den E v))). destruct (just_pos bm z ls B _ UT UV RV) as [A C]. fin A C.
      - exists (ONeg (bv_unsigned (den E v) - 2 ^ 64)). destruct (just_negu bm z ls B _ UT UV RV) as [A C]. fin A C. }
  assert (TSV : bv_unsigned (den E tsv) = t0).
  { revert CI. pose proof (G2.litZ_sound E tv t0 LT) as [TV _].
    repeat match goal with
    | |- (match ?x with _ => _ end) = _ -> _ => destruct x
    | |- (if ?c then _ else _) = _ -> _ => destruct c
    | |- None = Some _ -> _ => discriminate
    | |- Some _ = Some _ -> _ => intros [= <-]; exact TV
    end. }
  rewrite TSV.
  destruct (G2.litZ_sound E tv t0 LT) as [TV TR]. rewrite TV in UT. fold B bm in UT.
  destruct (Z.eqb_spec t0 T_NIL) as [->|N0].
  { clear CI. rewrite Z.mod_small in UT by (unfold T_NIL; lia). split; [unfold T_NIL; lia|]. exists ONil. destruct (just_nil bm z ls B UT) as [A C].
    fin A C. }
  destruct (Z.eqb_spec t0 T_BOOLEAN) as [->|N1].
  { destruct (cell_at r (b + 8) 1%uint63) as [bv|] eqn:CB; [|discriminate]. destruct (G2.litZ bv) as [x|] eqn:LB; [|discriminate].
    destruct ((x =? 0) || (x =? 1)) eqn:X01; [|discriminate]. clear CI.
    destruct (cell_at_u8_s segs priv E m k r (b + 8) bv RO K ltac:(lia) ltac:(lia) CB) as (UB & _ & _).
    destruct (G2.litZ_sound E bv x LB) as [BV BR]. rewrite BV in UB. replace (bv_unsigned (ev E k) + (b + 8)) with (B + 8) in UB by (subst B; lia). fold bm in UB.
    rewrite Z.mod_small in UT by (unfold T_BOOLEAN; lia). split; [unfold T_BOOLEAN; lia|].
    exists (OBool (x =? 1)). destruct (just_bool bm z ls B (x =? 1) UT) as [A C]; [| fin A C].
    rewrite Z.mod_small in UB by lia.
    apply orb_prop in X01 as [Hb|Hb]; apply Z.eqb_eq in Hb; subst x;
      [change (if 0 =? 1 then 1 else 0) with 0| change (if 1 =? 1 then 1 else 0) with 1]; exact UB. }
  destruct ((t0 =? T_POSINT) || (t0 =? T_NEGINT) || (t0 =? T_FLOAT64) || (t0 =? T_FLOAT32)) eqn:C4.
  { destruct (cell_at r (b + 8) 8%uint63) as [v|] eqn:CV; [|discriminate]. clear CI.
    destruct (cell_at_u64_s segs priv E m k r (b + 8) v RO K ltac:(lia) ltac:(lia) CV) as (UV & _ & _).
    replace (bv_unsigned (ev E k) + (b + 8)) with (B + 8) in UV by (subst B; lia). fold bm in UV.
    pose proof (bv_unsigned_in_range _ (den E v)) as RV. rewrite bv_modulus_64, two64_eq in RV.
    assert (T10 : 0 <= t0 <= 10) by (unfold T_POSINT, T_NEGINT, T_FLOAT64, T_FLOAT32 in C4; lia).
    rewrite Z.mod_small in UT by lia. split; [exact T10|].
    apply orb_prop in C4 as [C4|C4]; [apply orb_prop in C4 as [C4|C4]; [apply orb_prop in C4 as [C4|C4]|]|]; apply Z.eqb_eq in C4; subst t0.
    - exists (OPos (bv_unsigned (den E v))). destruct (just_pos bm z ls B _ UT UV RV) as [A C]. fin A C.
    - exists (ONeg (bv_unsigned (den E v) - 2 ^ 64)). destruct (just_negu bm z ls B _ UT UV RV) as [A C]. fin A C.
    - exists (OF64 (bv_unsigned (den E v))). destruct (just_f64 bm z ls B _ UT UV) as [A C]. fin A C.
    - exists (OF32 (bv_unsigned (den E v))). destruct (just_f32 bm z ls B _ UT UV) as [A C]. fin A C. }
  destruct ((t0 =? T_ARRAY) || (t0 =? T_MAP) || (t0 =? T_STR) || (t0 =? T_BIN)) eqn:C2; [|discriminate].
  destruct (cell_at r (b + 8) 4%uint63) as [nv|] eqn:CN; [|discriminate]. destruct (cell_at r (b + 16) 8%uint63) as [pv|] eqn:CP; [|discriminate].
  destruct (G2.litZ nv) as [n|] eqn:LN; [|discriminate]. destruct (G2.litZ pv) as [p|] eqn:LP; [|discriminate].
  destruct ((n =? 0) && (p =? 0)) eqn:NP; [|discriminate]. clear CI.
  apply andb_prop in NP as [N0' P0]. apply Z.eqb_eq in N0'. apply Z.eqb_eq in P0. subst n p.
  destruct (cell_at_u32_s segs priv E m k r (b + 8) nv RO K ltac:(lia) ltac:(lia) CN) as (UN & _ & _).
  destruct (cell_at_u64_s segs priv E m k r (b + 16) pv RO K ltac:(lia) ltac:(lia) CP) as (UP & _ & _).
  destruct (G2.litZ_sound E nv 0 LN) as [NV _]. destruct (G2.litZ_sound E pv 0 LP) as [PV _].
  rewrite NV in UN. rewrite PV in UP.
  replace (bv_unsigned (ev E k) + (b + 8)) with (B + 8) in UN by (subst B; lia). replace (bv_unsigned (ev E k) + (b + 16)) with (B + 16) in UP by (subst B; lia).
  fold bm in UN. fold bm in UP. change (0 mod 2 ^ 32) with 0 in UN.
  assert (T10 : 0 <= t0 <= 10) by (unfold T_ARRAY, T_MAP, T_STR, T_BIN in C2; lia). rewrite Z.mod_small in UT by lia. split; [exact T10|].
  apply orb_prop in C2 as [C2|C2]; [apply orb_prop in C2 as [C2|C2]; [apply orb_prop in C2 as [C2|C2]|]|]; apply Z.eqb_eq in C2; subst t0.
  - exists (OArr 0 []). destruct (just_empty_arr bm z ls B UT UN UP) as [A C]. fin A C.
  - exists (OMap 0 []). destruct (just_empty_map bm z ls B UT UN UP) as [A C]. fin A C.
  - exists (OStr 0 0). destruct (just_str bm z ls B 0 0 UT UN UP ltac:(unfold LIMIT; lia) ltac:(intros _; reflexivity) ltac:(intros X; exfalso; exact (X eq_refl))) as [A C]. fin A C.
  - exists (OBin 0 0). destruct (just_bin bm z ls B 0 0 UT UN UP ltac:(unfold LIMIT; lia) ltac:(intros _; reflexivity) ltac:(intros X; exfalso; exact (X eq_refl))) as [A C]. fin A C.
Qed.

Lemma g2z_apply_sound : forall E st ms model sts,
  st_ok segs OPS E st ms model -> g2z_apply st = Some sts -> exists st', In st' sts /\ st_ok segs OPS E st' ms model.
Proof.
  intros E st ms model sts HS AP.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  unfold g2z_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct root as [|k1 oR| | | | | | | | |]; try discriminate.
  destruct (okey oR) as [key|] eqn:OK; [|discriminate]. destruct (IMap.find k1 (s_regs st)) as [r1|] eqn:F1; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  destruct (complete_item_at r1 (keyZ key)) as [tsv|] eqn:CI; [|discriminate].
  destruct (GPot.GPot.pot_scan_c (s_facts st) aw ws) as [sc|] eqn:SCAN; [|discriminate].
  pose proof (GPot.GPot.pot_scan_c_ok E (s_facts st) aw ws sc Pfacts SCAN) as SCOK.
  cbv beta zeta in AP.

  assert (CHOICE : exists rt nf, In (surg st [] [] (mk_args 2%uint63 aw (GPot.GPot.pot_lit sc GPot.GPot.D_ITEMw ws) [VP k1 oR; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD;
                                                                         rt; VL wzero; VL wzero; zh]) nf (s_next st)) sts
                                 /\ den E rt = den E tsv /\ Forall (fact_holds E) nf).
  { destruct (G2.int_tag tsv) eqn:IT.
    - injection AP as <-. destruct (G2.int_tag_sound E tsv IT) as [T2|T3].
      + exists (VL (wlit 2%uint63)), [FEq tsv (VL (wlit 2%uint63))]. split; [left; reflexivity|].
        assert (EQ : den E (VL (wlit 2%uint63)) = den E tsv) by (apply bv_eq; cbn [den]; rewrite wbv_unsigned, wlit_ok, T2; reflexivity).
        split; [exact EQ|]. constructor; [cbn [fact_holds]; symmetry; exact EQ| constructor].
      + exists (VL (wlit 3%uint63)), [FEq tsv (VL (wlit 3%uint63))]. split; [right; left; reflexivity|].
        assert (EQ : den E (VL (wlit 3%uint63)) = den E tsv) by (apply bv_eq; cbn [den]; rewrite wbv_unsigned, wlit_ok, T3; reflexivity).
        split; [exact EQ|]. constructor; [cbn [fact_holds]; symmetry; exact EQ| constructor].
    - injection AP as <-. exists tsv, []. split; [left; reflexivity|]. split; [reflexivity| constructor]. }
  destruct CHOICE as (rt & nf & INsts & RTEQ & HNF). eexists. split; [exact INsts|].
  apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND K62]. apply andb_prop in COND as [COND OK4]. apply andb_prop in COND as [CBCE K10].
  apply sv_eqb_eq in CBCE. apply negb_true_iff in K10. apply Z.ltb_lt in K62. apply Z.ltb_lt in WLEN.
  pose proof (keyZ_range key) as KRR.

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
  assert (Lroot' : u_root g = bv_unsigned (den E (VP k1 oR))) by exact Lroot.
  pose proof P as (VC & EC & SC & CC & VV & EV & SV' & CV & LV & DL' & LA & ZV).

  assert (NIL : u_levels g = []).
  { assert (X : v_begin (u_cstk g) = v_end (u_cstk g)) by (rewrite Lcb, Lce, CBCE; reflexivity).
    unfold v_end in X. rewrite EC, SC in X. unfold u_D in X. destruct (u_levels g); [reflexivity| cbn [length] in X; lia]. }

  pose proof (Preg k1 r1 F1) as RO1.
  destruct (complete_item_at_sound (s_priv st) E (ms_mem ms) k1 r1 (keyZ key) tsv (u_zone g) (u_levels g) RO1 K10 ltac:(unfold two62Z in *; lia) K62 CI)
    as (T10 & o0 & TREE & TLC & NOB & OTY & OCNT & OPTR & KIDS & DEP1 & PK10). cbv zeta in T10, OTY.
  assert (ADDR : u_cur_slot g = bv_unsigned (ev E k1) + keyZ key).
  { unfold u_cur_slot. rewrite NIL. cbn [cur_slot rev]. rewrite Lroot'.
    destruct TREE as [OA _]. pose proof (proj1 (proj1 (obj_at_split _ _ _) OA)) as HT. destruct HT as [UT _].
    assert (RNG : 0 <= bv_unsigned (ev E k1) + keyZ key < two64).
    { unfold u32_at in UT. pose proof (rdZ_range segs (ms_mem ms) 3 _ _ UT) as X. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in X. lia. }
    rewrite (den_VP_addr E k1 oR key OK) by (unfold addrZ; exact RNG). rewrite Z_to_bv_unsigned. unfold addrZ, bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. exact RNG. }

  assert (LEN' : Z.of_nat (length (GPot.GPot.pot_lit sc GPot.GPot.D_ITEMw ws)) < two63) by (rewrite GPot.GPot.pot_lit_length; exact LEN).
  assert (DITEM : 0 <= w2Z GPot.GPot.D_ITEMw <= 2 ^ 20) by (change (w2Z GPot.GPot.D_ITEMw) with 40; lia).
  pose proof (GPot.GPot.scan_oldb E ws sc SCOK) as OLDB. pose proof (GPot.GPot.lit_newb E ws sc GPot.GPot.D_ITEMw SCOK DITEM) as NEWB.
  apply (surgery_sound segs OPS E (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [] [] (mk_args 2%uint63 aw (GPot.GPot.pot_lit sc GPot.GPot.D_ITEMw ws) _) nf (s_next st)).
  - intros k [].
  - constructor.
  - intros k r' [].
  - intros k r' [].
  - intros k r' a [].
  - intros ka ra kb rb a [].
  - rewrite (ho_holds _ _ _ _ _ HOPS).
    exists 2, (den E aw), (map (wden E) (GPot.GPot.pot_lit sc GPot.GPot.D_ITEMw ws)), (map (den E) [VP k1 oR; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; tsv; VL wzero; VL wzero; zh]), LB.
    split; [cbn [map]; rewrite <- RTEQ; apply mk_args_sound; exact LEN'|].
    split; [exact (aw_keep segs IMGX AW _ _ _ _ _ _ HA (GPot.GPot.wins_keep_pot_set E sc _ _ OLDB NEWB LB))|].
    split; [exact (GPot.GPot.windows_wf_pot_set E sc _ _ OLDB NEWB LB _ (aw_ceiling_small segs IMGX AW model) WF)|].
    cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. cbn [map decode_uc].
    exists g. split; [| split; [exact P| split; [exact O| split; [| split; [exact M| split; [| split; [split; [exact (proj1 AX)| intros X; discriminate X]| exact (GPot.GPot.seal_ok_pot_set E sc _ _ _ SE)]]]]]]].
    +
      enough (LINK' : link (UC (bv_unsigned (den E (VP k1 oR))) (bv_unsigned (den E cb)) (bv_unsigned (den E ce)) (bv_unsigned (den E ccap))
                             (bv_unsigned (den E vb)) (bv_unsigned (den E ve)) (bv_unsigned (den E vcap)) (bv_unsigned (den E zptr))
                             (bv_unsigned (den E zfree)) (bv_unsigned (den E c0)) (bv_unsigned (den E slot)) (bv_unsigned (den E tD))
                             (bv_unsigned (den E restD)) (bv_unsigned (den E tsv)) (bv_unsigned (den E (VL wzero)))
                             (bv_unsigned (den E (VL wzero)))) g) by exact LINK'.
      unfold link. cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1].
      split; [exact Lroot'|]. split; [exact Lcb|]. split; [exact Lce|]. split; [exact Lccap|]. split; [exact Lvb|]. split; [exact Lve|].
      split; [exact Lvcap|]. split; [exact Lzp|]. split; [exact Lzf|]. split; [exact Lc0|]. intros X. exfalso. exact (X NIL).
    +
      apply GPot.GPot.wins_ok_pot_set.
      unfold wins_ok in *. apply Forall_forall. intros w Hw NS.
      apply in_map_iff in Hw as (x & <- & Hx).
      destruct (proj1 (Forall_forall _ _) Wk (wden E x) (in_map _ _ _ Hx) NS) as [D1|[NB SO]]; [left; exact D1| right].
      split; [exact NB|].
      unfold sub_ok in SO |- *. cbv zeta in SO |- *.
      destruct SO as [A|[A|[(KK & lD & HlD & I2 & I3)|A]]]; [left; exact A| right; left; exact A| | right; right; right; exact A].
      exfalso. pose proof (only_kind_sound E 4 None ws OK4 x Hx KK) as X. discriminate X.
    +
      intros _. cbv zeta. exists o0. rewrite ADDR. destruct TREE as [OA TW].
      split; [exact TW|]. split; [exact KIDS|]. split; [intros X; exfalso; exact (X NIL)|].
      split.
      { intros _. cbn [c_rootT c_n1 c_P1]. change (bv_unsigned (den E (VL wzero))) with (w2Z wzero). change (w2Z wzero) with 0.
        rewrite OTY, OCNT, OPTR. repeat split; reflexivity. }
      split; [exact TLC|]. split; [unfold bodies_ok; rewrite NOB; constructor|]. split; [rewrite DEP1, NIL; cbn [length]; lia|].

      destruct (proj2 AX eq_refl) as (S0 & KP0 & PA0). exists S0. split; [exact KP0|].
      apply (GPot.GPot.pot_at_set E ws ws sc _ _ SCOK); [intros x Hx; left; exact Hx|].
      pose proof (GPot.GPot.lit_value E ws sc GPot.GPot.D_ITEMw _ SCOK PA0 DITEM) as LV0. destruct sc as [lo|]; [| exact I].
      rewrite LV0, (Pot.Pot.pot_val_item (u_levels g) S0 (Pot.Pot.pk10_tree o0)), PK10. reflexivity.
  -
    intros a FPa. split; [| intros k r' []]. left. unfold FP in FPa |- *. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa |- *.
    apply (proj1 (heap_fp_iff IMGX _ 2 _ (map (wden E) (GPot.GPot.pot_lit sc GPot.GPot.D_ITEMw ws)) _ a (mk_args_sound E 2%uint63 aw _ _ LEN'))) in FPa as (RA & NI & NW).
    assert (NW' : ~ in_ws (map (wden E) ws) a) by (intros X; apply NW; apply GPot.GPot.in_ws_pot_set; exact X).
    apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E) ws) _ a DEC)). auto.
  - exact HNF.
Qed.

Theorem g2z_sound : contract_sound segs OPS MP PB g2z_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [g2z_contract c_apply] in HA.
  destruct (g2z_apply_sound E st ms model sts HS HA) as (st' & IN & OK').
  exact (Hk st' IN E ms model (env_ext_refl (s_next st) E) HMP OK').
Qed.

End Sound.
End WithPc.
End G2Z.
