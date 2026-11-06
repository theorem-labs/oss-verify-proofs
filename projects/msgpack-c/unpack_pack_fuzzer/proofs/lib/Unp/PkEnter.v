(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Ops Tree KidsFacts CapLen TdEnter PkOps PkLib GLib GWin PkStack PkAux.
Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Seal OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Pot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GPot PotDrop PkU PkUSwap PkUAdd PkCost.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UO UG GW TR PK PKL PkStack PkAux CapLen.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.

Module PkEnter.
Import TdEnter.

Section WithPc.
Variable ENTER_PC : int.

Definition HANDW : w64 := wlit 6917529027775299584%uint63.
Definition pkenter_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 2%uint63 then
      match ca with
      | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
          let n := s_next st in
          match cb, vb, zh with
          | VP kCB oCB, VP kVB oVB, VP kZ oZ =>

            match cap_len kCB ccap, cap_len kVB vcap with
            | Some lenC, Some lenV =>
              if common_ok st ws && kinds_lit ws && match decide_eq (s_facts st) cb ce with Some true => true | _ => false end
                 && weqb oCB wzero && weqb oVB wzero && weqb oZ wzero
                 && negb (PrimInt63.eqb kCB kVB)
                 && negb (PrimInt63.eqb kCB 0%uint63) && negb (PrimInt63.eqb kCB 1%uint63)
                 && negb (PrimInt63.eqb kVB 0%uint63) && negb (PrimInt63.eqb kVB 1%uint63)
              then
                match sub_anchors st ws, IMap.find kZ (s_regs st) with
                | Some ks, Some rZ =>
                    if anchor_free st ks kCB && anchor_free st ks kVB
                       && match cell_at rZ 24 8%uint63 with Some v => sv_eqb v c0 | None => false end
                    then

                      match GPot.pot_scan (s_facts st) ws with
                      | None => None
                      | Some sc =>
                      let kept := List.filter is_kept (PotDrop.drop_of sc ws) in
                      let ws' := kept ++ [(VP kCB wzero, lenC, VL (wlit 1%uint63)); (VP kVB wzero, lenV, VL (wlit 1%uint63))] in
                      let ca' := [root; rootT; n1; P1; zh; c0; VL wzero; VL wzero; VL wzero; VL wzero; VL wzero; VL wzero; VL wzero;
                                  VL wzero; VL wzero; VL wzero; VL wzero] in
                      let uw := match sc with Some _ => [PkU.mk_pku false n] | None => [] end in
                      let uf := match sc with
                                | Some lo => [FEq (VAlu ALU_ADD (VL HANDW) (VAlu ALU_SLL (VP n wzero) (VL GPot.wtwo))) lo; FRange n wzero PkU.UMAX]
                                | None => [] end in
                      let nx := match sc with Some _ => PrimInt63.add n 1%uint63 | None => n end in
                      if match sc with Some lo => sv_vars_below n lo | None => true end
                         && match PkU.scan (s_facts st) ws' with Some None => true | _ => false end
                      then

                      Some [surg st ks [(kCB, empty_region lenC); (kVB, empty_region lenV)] (mk_args 3%uint63 aw (ws' ++ uw) ca') (KF.kids_facts n1 P1 ++ uf) nx]
                      else None
                      end
                    else None
                | _, _ => None
                end
              else None
            | _, _ => None
            end
          | _, _, _ => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Definition pkenter_contract : contract := Contract ENTER_PC pkenter_apply.
End WithPc.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW2 : forall ca LB ws m, cw_holds CW 2 ca LB ws m ->
  match decode_uc ca with Some u => unp_client segs 2 u LB ws m | None => False end.
Hypothesis CW3' : forall ca LB ws m, PK.cw_pk_holds segs ca LB ws m -> cw_holds CW 3 ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Local Ltac inl := cbn [In]; repeat (first [left; reflexivity| right]).

Lemma pkenter_sound_main : forall E st ms model st',
  st_ok segs OPS E st ms model -> pkenter_apply st = Some [st'] ->
  (forall md aw ws ca lo, the_op st = Some (md, aw, ws, ca) -> GPot.pot_scan (s_facts st) ws = Some (Some lo) ->
     ev E (s_next st) = Z_to_bv 64 ((bv_unsigned (den E lo) - POT_BASE - Pot.Pot.Q0) / 4)) ->
  st_ok segs OPS E st' ms model.
Proof.
  intros E st ms model st' HS AP HEV.
  unfold pkenter_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 2) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbv zeta in AP.
  destruct cb as [|kCB oCB| | | | | | | | |]; try discriminate.
  destruct vb as [|kVB oVB| | | | | | | | |]; try discriminate.
  destruct zh as [|kZ oZ| | | | | | | | |]; try discriminate.
  destruct (cap_len kCB ccap) as [lenC|] eqn:CLC; [|discriminate].
  destruct (cap_len kVB vcap) as [lenV|] eqn:CLV; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  apply andb_prop in COND as [COND KV1]. apply andb_prop in COND as [COND KV0]. apply andb_prop in COND as [COND KC1]. apply andb_prop in COND as [COND KC0].
  apply andb_prop in COND as [COND KCV].
  apply andb_prop in COND as [COND OZ]. apply andb_prop in COND as [COND OV]. apply andb_prop in COND as [COND OC].
  apply andb_prop in COND as [COND CBE]. apply andb_prop in COND as [COND KL].
  unfold common_ok in COND. apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND NLT]. apply andb_prop in COND as [VB NPOS].
  apply Z.ltb_lt in WLEN. apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS.
  apply (proj1 (weqb_ok _ _)) in OC. apply (proj1 (weqb_ok _ _)) in OV. apply (proj1 (weqb_ok _ _)) in OZ. subst oCB oVB oZ.
  apply negb_true_iff in KCV. apply negb_true_iff in KC0. apply negb_true_iff in KC1. apply negb_true_iff in KV0. apply negb_true_iff in KV1.
  match type of CBE with (match ?d with _ => _ end) = true => destruct d as [[]|] eqn:DQ; try discriminate CBE end. clear CBE.
  destruct (sub_anchors st ws) as [ks|] eqn:SA; [|discriminate].
  destruct (IMap.find kZ (s_regs st)) as [rZ|] eqn:FZ; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND2; [|discriminate] end.
  destruct (GPot.pot_scan (s_facts st) ws) as [sc|] eqn:PSC; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND3; [|discriminate] end.
  apply andb_prop in COND3 as [VBLO NOU].
  injection AP as <-.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (decide_eq_sound E (s_facts st) Pfacts _ _ _ DQ) as CBE. apply (proj1 (eqb_iff _ _ true)) in CBE.
  destruct (the_op_full st 2%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  destruct (sub_anchors_spec st ws ks SA) as [KS1 KS2].
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DEC.
  rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 2%uint63) with 2 in HC.
  apply CW2 in HC. cbn [map decode_uc] in HC.
  destruct HC as (g & L & P & O & Wk & M & CS0 & _ & SEALu).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap, Lzp, Lzf, Lc0, LD.
  change (u_root g = bv_unsigned (den E root)) in Lroot.
  change (v_begin (u_cstk g) = bv_unsigned (den E (VP kCB wzero))) in Lcb. change (v_end (u_cstk g) = bv_unsigned (den E ce)) in Lce. rewrite <- CBE in Lce.
  change (z_head (u_zone g) = bv_unsigned (den E c0)) in Lc0.
  pose proof (UO.pf g P) as (VC & EC & SC & VV & EV & SV' & LVL & LA & ZV).
  pose proof ZV as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7).

  assert (D0 : u_levels g = []).
  { unfold v_end in Lce. rewrite Lcb, EC, SC in Lce. unfold u_D in Lce. destruct (u_levels g); [reflexivity| cbn [length] in Lce; lia]. }
  destruct (CS0 eq_refl) as (t & TWt & KAt & _ & ROOTP & TLC & BOD & TDEPTH & TPOT).
  destruct (ROOTP D0) as (RT & RN & RP). cbn [c_rootT c_n1 c_P1] in RT, RN, RP.
  assert (CUR : u_cur_slot g = u_root g) by (unfold u_cur_slot, cur_slot; rewrite D0; reflexivity).
  rewrite CUR in TLC. rewrite D0 in TLC, BOD.

  pose proof (proj1 O _ (UO.owned_cstk g)) as CLB. pose proof (proj1 O _ (UO.owned_vstk g)) as VLB.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (cstk_block g) HA CLB) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (vstk_block g) HA VLB) as (Bv1 & Bv2 & Bv3 & _ & Bv5).
  unfold cstk_block in Bc1, Bc2, Bc3. unfold vstk_block in Bv1, Bv2, Bv3. cbn [fst snd] in Bc1, Bc2, Bc3, Bv1, Bv2, Bv3.
  pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold Mem.two62Z in CEIL.
  pose proof (UO.disj_cv g LB O) as DCV.
  assert (CBV : bv_unsigned (ev E kCB) = v_begin (u_cstk g)) by (rewrite Lcb; symmetry; exact (den_VP0 E kCB wzero (weqb_refl _))).
  assert (VBV : bv_unsigned (ev E kVB) = v_begin (u_vstk g)) by (rewrite Lvb; symmetry; exact (den_VP0 E kVB wzero (weqb_refl _))).
  assert (SZC : bv_unsigned (den E lenC) = v_bytes (u_cstk g)).
  { apply (cap_len_sound E kCB ccap lenC _ CLC); [| lia | rewrite CBV; lia].
    rewrite <- Lccap, CBV. unfold v_capend, v_bytes. reflexivity. }
  assert (SZV : bv_unsigned (den E lenV) = v_bytes (u_vstk g)).
  { apply (cap_len_sound E kVB vcap lenV _ CLV); [| lia | rewrite VBV; lia].
    rewrite <- Lvcap, VBV. unfold v_capend, v_bytes. reflexivity. }
  assert (INW : forall a b c, In (a, b, c) ws -> In a (op_args o) /\ In b (op_args o) /\ In c (op_args o)).
  { intros a b c Hw. destruct (in_flat_windows ws a b c Hw) as (Ia & Ib & Ic). rewrite ARGS.
    repeat split; right; right; right; apply in_app_iff; left; assumption. }
  assert (INCA : forall v, In v [root; VP kCB wzero; ce; ccap; VP kVB wzero; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; VP kZ wzero] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E) ws) a -> FP OPS E (op_args o) a).
  { intros a RA NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS).
    apply (proj2 (heap_fp_iff IMGX _ 2 _ (map (wden E) ws) _ a DEC)). auto. }

  assert (SUBR : forall w3 a, In w3 ws -> is_sub w3 = true -> in_iv (w_iv (wden E w3)) a ->
            exists k0 r0, In k0 ks /\ IMap.find k0 (s_regs st) = Some r0 /\ inR E k0 r0 a).
  { intros w3 a Hw3 SB Ha. destruct (KS2 w3 Hw3 SB) as (k0 & Hk0 & AN).
    destruct (sub_anchor_spec st w3 k0 AN) as (len & kd & r0 & -> & K0 & K1 & F0 & LO & W0 & HI).
    exists k0, r0. split; [exact Hk0|]. split; [exact F0|].
    unfold inR, loZ, hiZ. rewrite LO, HI. change (keyZ 0%uint63) with 0.
    unfold wden, w_iv, in_iv in Ha. cbn [w_lo w_len fst snd] in Ha. rewrite (den_VP0 E k0 wzero (weqb_refl _)) in Ha. lia. }
  assert (OWNB : forall ob a, In ob (UO.owned g) -> in_iv ob a ->
            (0 <= a /\ a < two64) /\ ~ in_ivs IMGX a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None /\
            (FP OPS E (op_args o) a \/ exists k0 r0, In k0 ks /\ IMap.find k0 (s_regs st) = Some r0 /\ inR E k0 r0 a)).
  { intros ob a Hob Ha. pose proof (proj1 O ob Hob) as OLB.
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model ob HA OLB) as (B1 & B2 & B3 & B4 & B5).
    destruct (aw_user_ok segs IMGX AW _ LB _ (ms_mem ms) model ob a HA OLB Ha) as [MAT NS].
    assert (RA : 0 <= a /\ a < two64) by (unfold in_iv in Ha; lia).
    split; [exact RA|]. split; [exact (B5 a Ha)|]. split; [exact MAT|]. split; [exact NS|].
    destruct (in_ws_dec (map (wden E) ws) a) as [IW|NW].
    - right. apply (proj1 (in_ws_map_iff E ws a)) in IW as (w3 & Hw3 & Hin).
      destruct (Z.eq_dec (w_kind (wden E w3)) K_STACK) as [K|NK].
      + exfalso. pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hw3)) as (_ & _ & _ & [[_ S]|[[K' _]|[K' _]]]).
        * unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. unfold in_iv in Ha. lia.
        * rewrite K in K'. discriminate.
        * rewrite K in K'. unfold K_SUB, K_STACK in K'. lia.
      + destruct (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ Hw3) NK) as [[_ D]|[NB SO]].
        * exfalso. exact (D ob Hob a Hin Ha).
        * apply (SUBR w3 a Hw3); [|exact Hin].
          pose proof (proj1 (forallb_forall _ _) KL w3 Hw3) as Q. cbn beta in Q. unfold is_sub.
          destruct (kind_of w3) as [kd|] eqn:KD; [|discriminate]. rewrite (kind_of_sound E w3 kd KD) in NK, NB.
          destruct SO as [(KK_ & _)|[(KK_ & _)|[(KK_ & _)|(KK_ & _)]]]; rewrite (kind_of_sound E w3 kd KD) in KK_; unfold K_CTOP, K_VTOP, K_SLOT, K_ZONE in KK_; subst kd; reflexivity.
    - left. exact (FPold a RA (B5 a Ha) NW). }

  assert (HIC : hiZ E (empty_region lenC) = v_bytes (u_cstk g)) by (unfold hiZ; cbn [empty_region rg_hi]; exact SZC).
  assert (HIV : hiZ E (empty_region lenV) = v_bytes (u_vstk g)) by (unfold hiZ; cbn [empty_region rg_hi]; exact SZV).
  assert (LOE : forall x, loZ (empty_region x) = 0) by (intros x; reflexivity).
  assert (REGC : region_ok segs (s_priv st) E (ms_mem ms) kCB (empty_region lenC)).
  { apply (region_ok_fresh segs (s_priv st) E (ms_mem ms) kCB (empty_region lenC) KC0).
    - apply IMap.bst_empty.
    - reflexivity.
    - rewrite LOE, CBV. lia.
    - rewrite HIC, CBV. unfold two64 in *. lia.
    - intros a Ha. rewrite LOE, HIC, CBV in Ha.
      destruct (OWNB (cstk_block g) a (UO.owned_cstk g) ltac:(unfold in_iv, cstk_block; cbn [fst snd]; lia)) as (_ & _ & MT & NS & _). split; [exact MT| exact NS].
    - intros gk gr F. cbn [empty_region rg_cells] in F. rewrite IMap.find_empty in F. discriminate. }
  assert (REGV : region_ok segs (s_priv st) E (ms_mem ms) kVB (empty_region lenV)).
  { apply (region_ok_fresh segs (s_priv st) E (ms_mem ms) kVB (empty_region lenV) KV0).
    - apply IMap.bst_empty.
    - reflexivity.
    - rewrite LOE, VBV. lia.
    - rewrite HIV, VBV. unfold two64 in *. lia.
    - intros a Ha. rewrite LOE, HIV, VBV in Ha.
      destruct (OWNB (vstk_block g) a (UO.owned_vstk g) ltac:(unfold in_iv, vstk_block; cbn [fst snd]; lia)) as (_ & _ & MT & NS & _). split; [exact MT| exact NS].
    - intros gk gr F. cbn [empty_region rg_cells] in F. rewrite IMap.find_empty in F. discriminate. }

  assert (SUBK : forall w3, In w3 ws -> is_kept w3 = false -> K_SUB <= w_kind (wden E w3) < K_GHOST).
  { intros w3 Hw3 IK. pose proof (kept_or_sub ws w3 KL Hw3 IK) as IS. unfold is_sub in IS. destruct (kind_of w3) as [kd|] eqn:KD; [|discriminate IS].
    rewrite (kind_of_sound E w3 kd KD). apply andb_prop in IS as [I1 I2]. apply Z.leb_le in I1. apply Z.leb_le in I2. unfold K_SUB, K_GHOST. lia. }

  destruct (PotDrop.drop_of_spec E (s_facts st) ws sc Pfacts PSC) as (DSUB & DOLD & DLEN).
  set (ws0 := PotDrop.drop_of sc ws) in *.
  set (kept := List.filter is_kept ws0) in *.
  set (ws' := kept ++ [(VP kCB wzero, lenC, VL (wlit 1%uint63)); (VP kVB wzero, lenV, VL (wlit 1%uint63))]) in *.
  assert (KEPT : forall w, In w kept -> In w ws /\ is_kept w = true) by (intros w Hw; apply filter_In in Hw; split; [exact (DSUB w (proj1 Hw))| exact (proj2 Hw)]).
  assert (KSEALu : Seal.seal_ok (map (wden E) kept) (z_chunks (u_zone g))).
  { apply (Seal.seal_ok_ws (map (wden E) ws)); [exact SEALu|]. intros w Hw _. apply in_map_iff in Hw as (w3 & <- & Hw3).
    apply in_map. exact (proj1 (KEPT w3 Hw3)). }
  assert (LENK : (length kept <= length ws)%nat).
  { assert (X : (length kept <= length ws0)%nat) by (subst kept; generalize ws0; clear; intros l; induction l as [|w l IH]; cbn; [lia|]; destruct (is_kept w); cbn; lia). lia. }
  assert (LEN' : Z.of_nat (length ws') < two63) by (subst ws'; rewrite length_app; cbn [length]; unfold two63; lia).
  assert (WNC : wden E (VP kCB wzero, lenC, VL (wlit 1%uint63)) = Win (v_begin (u_cstk g)) (v_bytes (u_cstk g)) K_BLOCK).
  { unfold wden. rewrite (den_VP0 E kCB wzero (weqb_refl _)), CBV, SZC. cbn [den]. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  assert (WNV : wden E (VP kVB wzero, lenV, VL (wlit 1%uint63)) = Win (v_begin (u_vstk g)) (v_bytes (u_vstk g)) K_BLOCK).
  { unfold wden. rewrite (den_VP0 E kVB wzero (weqb_refl _)), VBV, SZV. cbn [den]. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  assert (WS' : map (wden E) ws' = map (wden E) kept ++ [Win (v_begin (u_cstk g)) (v_bytes (u_cstk g)) K_BLOCK; Win (v_begin (u_vstk g)) (v_bytes (u_vstk g)) K_BLOCK]).
  { subst ws'. rewrite map_app. cbn [map]. rewrite WNC, WNV. reflexivity. }

  set (n := s_next st) in *.
  set (uw := match sc with Some _ => [PkU.mk_pku false n] | None => [] end) in *.
  set (uf := match sc with Some lo => [FEq (VAlu ALU_ADD (VL HANDW) (VAlu ALU_SLL (VP n wzero) (VL GPot.wtwo))) lo; FRange n wzero PkU.UMAX] | None => [] end) in *.
  set (nx := match sc with Some _ => PrimInt63.add n 1%uint63 | None => n end) in *.
  assert (LENn : Z.of_nat (length (ws' ++ uw)) < two63).
  { rewrite length_app. assert (X : (length uw <= 1)%nat) by (subst uw; destruct sc; cbn [length]; lia). clear - LEN' X WLEN LENK. subst ws'. rewrite length_app in *. cbn [length] in *. unfold two63 in *. lia. }
  assert (UVAL : forall lo, sc = Some lo -> bv_unsigned (ev E n) = PK.pk10_tree t /\ PK.pk10_tree t <= 2 ^ 41 /\ bv_unsigned (den E lo) = POT_BASE + Pot.Pot.Q0 + 4 * PK.pk10_tree t).
  { intros lo ->. pose proof (UO.pot_handover (map (wden E) ws) _ g t D0 TPOT) as PA.
    pose proof (GPot.pot_scan_ok E (s_facts st) ws (Some lo) Pfacts PSC) as SOK.
    pose proof (GPot.scan_value E ws lo _ SOK PA) as VAL. destruct SOK as (_ & B & _).
    change (Pot.Pot.pk10_tree t) with (PK.pk10_tree t) in VAL.
    pose proof (PkCost.pk10_tree_nonneg _ _ t TWt) as NN.
    assert (Q : Pot.Pot.Q0 = 2 ^ 27) by reflexivity.
    rewrite (HEV _ _ _ _ lo eq_refl PSC), VAL.
    replace (POT_BASE + (Pot.Pot.Q0 + 4 * PK.pk10_tree t) - POT_BASE - Pot.Pot.Q0) with (PK.pk10_tree t * 4) by lia.
    rewrite Z.div_mul by lia. split; [| split; [| lia]].
    - apply u64_of_Z. unfold two64. rewrite Q in *. lia.
    - rewrite Q in *. lia. }
  assert (PU : forall x, In x (map (wden E) uw) -> exists q, pku_val x = Some q).
  { intros x Hx. subst uw. destruct sc as [lo|]; [| destruct Hx]. destruct Hx as [<-|[]]. destruct (UVAL lo eq_refl) as (U1 & U2 & _).
    eexists. apply (PkU.mk_pku_val E false n). rewrite U1. exact U2. }
  assert (NOUw : forall x, In x (map (wden E) ws') -> pku_val x = None).
  { intros x Hx. apply in_map_iff in Hx as (y & <- & Hy). destruct (PkU.scan (s_facts st) ws') as [[?|]|] eqn:SCN; try discriminate NOU.
    exact (PkU.scan_none E (s_facts st) Pfacts ws' SCN y Hy). }

  apply (surgery_sound segs OPS E (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH ks
           [(kCB, empty_region lenC); (kVB, empty_region lenV)] _ _ nx).
  -   intros k Hk. destruct (KS1 k Hk) as (w3 & Hw3 & SB & AN).
    destruct (sub_anchor_spec st w3 k AN) as (len & kd & r0 & -> & K0 & K1 & F0 & LO & W0 & HI). split; [exact K0|]. exists r0. auto.
  -   cbn [map fst]. constructor; [| constructor; [intros []| constructor]]. intros [X|[]]. rewrite X, Uint63.eqb_refl in KCV. discriminate.
  -   intros k r [X|[X|[]]]; injection X as <- <-; assumption.
  -   intros k r [X|[X|[]]]; injection X as <- <-; assumption.
  -   intros k r a [X|[X|[]]] IR; injection X as <- <-; unfold inR in IR; rewrite LOE in IR.
    + rewrite HIC, CBV in IR. exact (proj2 (proj2 (proj2 (proj2 (OWNB (cstk_block g) a (UO.owned_cstk g) ltac:(unfold in_iv, cstk_block; cbn [fst snd]; lia)))))).
    + rewrite HIV, VBV in IR. exact (proj2 (proj2 (proj2 (proj2 (OWNB (vstk_block g) a (UO.owned_vstk g) ltac:(unfold in_iv, vstk_block; cbn [fst snd]; lia)))))).
  -   intros k1 r1 k2 r2 a [X1|[X1|[]]] [X2|[X2|[]]] NE12; injection X1 as <- <-; injection X2 as <- <-; try contradiction;
      unfold inR; rewrite !LOE, ?HIC, ?HIV, ?CBV, ?VBV; unfold rdisj in DCV; lia.
  -   rewrite (ho_holds _ _ _ _ _ HOPS).
    eexists 3, (den E aw), (map (wden E) (ws' ++ uw)), _, LB.
    split; [apply (mk_args_sound E 3%uint63 aw (ws' ++ uw) _ LENn)|]. rewrite map_app. split.
    { refine (aw_keep segs IMGX AW _ _ _ _ _ _ _ (PkUAdd.add_keep _ _ PU LB)).
      rewrite WS'. refine (aw_keep segs IMGX AW _ _ _ _ _ _ (aw_keep segs IMGX AW _ _ _ _ _ _ HA (PotDrop.drop_keep E LB ws ws0 DSUB DOLD)) _).
      match type of Wk with wins_ok ?mdz _ _ => assert (Wk0 : wins_ok mdz g (map (wden E) ws0)) end.
      { unfold wins_ok in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
        exact (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ (DSUB x Hx))). }
      apply (UOK.unp_wins_keep _ g LB _ _ P O Wk0).
      - intros w Hw. apply in_app_iff in Hw as [Hw|[<-|[<-|[]]]].
        + left. apply in_map_iff in Hw as (w3 & <- & Hw3). apply in_map. exact (proj1 (proj1 (filter_In _ _ _) Hw3)).
        + right. right. split; [reflexivity|]. exact (UO.owned_cstk g).
        + right. right. split; [reflexivity|]. exact (UO.owned_vstk g).
      - intros w Hw. apply in_map_iff in Hw as (w3 & <- & Hw3). destruct (is_kept w3) eqn:IK.
        + left. apply in_app_iff. left. apply in_map. subst kept. apply filter_In. split; assumption.
        + right. left. exact (SUBK w3 (DSUB w3 Hw3) IK). }
    split.
    +   apply (PkUAdd.add_wf _ _ PU segs IMGX AW LB _ (aw_ceiling_small segs IMGX AW model)).
      rewrite WS'. unfold windows_wf in *. apply Forall_app. split.
      * apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (w3 & <- & Hw3). destruct (KEPT w3 Hw3) as [Hw3' _].
        exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hw3')).
      * constructor; [| constructor; [|constructor]]; unfold window_wf; cbn [w_lo w_len w_kind w_iv].
        -- split; [lia|]. split; [lia|]. split; [unfold two64 in *; lia|]. right; left. split; [reflexivity|]. exact CLB.
        -- split; [lia|]. split; [lia|]. split; [unfold two64 in *; lia|]. right; left. split; [reflexivity|]. exact VLB.
    +   apply CW3'. unfold cw_pk_holds. cbn [map decode_pk].
      set (g' := PKG t (mkVec 0 0 0 ELEM_SIZE) (u_zone g)).
      assert (OWE : PK.owned g' = map chunk_block (z_chunks (u_zone g))) by reflexivity.
      exists g', []. split; [| split; [| split; [| split]]].
      *   unfold link_pk. cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP last_opt rev].
        change (k_tree g') with t. change (k_zone g') with (u_zone g). change (k_evec g') with (mkVec 0 0 0 ELEM_SIZE).
        split; [exact RT|]. split; [unfold UO.obj_cnt in RN; exact RN|]. split; [exact RP|]. split; [exact Lc0|].
        cbn [den v_begin v_end v_capend v_elt v_size v_cap]. rewrite !wbv_unsigned, !wzero_ok.
        repeat split; first [reflexivity| lia| intros X; exfalso; exact (X eq_refl)].
      *   unfold pure_pk. change (k_tree g') with t. change (k_zone g') with (u_zone g). change (k_evec g') with (mkVec 0 0 0 ELEM_SIZE).
        cbn [levels_ok v_elt v_size v_begin v_cap v_capend length Z.of_nat].
        split; [exact I|]. split; [reflexivity|]. split; [reflexivity|]. split; [left; repeat split; reflexivity|]. split; [| split; [exact ZV| clear - TDEPTH D0; rewrite D0 in TDEPTH; cbn [length] in TDEPTH; lia]].
        unfold v_capend; cbn [v_begin v_elt v_cap]; rewrite Z.mul_0_r, Z.add_0_r; unfold two64; apply Z.pow_pos_nonneg || idtac; lia.
      *   split; [| rewrite OWE].
        -- rewrite OWE. intros b Hb. apply in_map_iff in Hb as (c & <- & Hc). exact (proj1 O _ (UO.owned_chunk g c Hc)).
        -- destruct O as [_ [O2 _]]. unfold UO.owned in O2. inversion O2 as [|x1 l1 F1 O3]; subst. inversion O3 as [|x2 l2 F2 O4]; subst. exact O4.
      *   apply (PkUAdd.add_wins_pk _ _ PU). unfold wins_pk. rewrite WS', OWE. apply Forall_app. split.
        -- apply Forall_forall. intros w Hw NK. apply in_map_iff in Hw as (w3 & <- & Hw3). destruct (KEPT w3 Hw3) as [Hw3' IK].
           pose proof (is_kept_kind E w3 IK) as KK.
           destruct (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ Hw3') NK) as [[KD D]|[NB SOk]].
           ++ left. split; [exact KD|]. intros b Hb. apply in_map_iff in Hb as (c & <- & Hc). exact (D (chunk_block c) (UO.owned_chunk g c Hc)).
           ++ exfalso. destruct SOk as [(KK_ & _)|[(KK_ & _)|[(KK_ & _)|(KK_ & _)]]]; unfold K_CTOP, K_VTOP, K_SLOT, K_ZONE in KK_; lia.
        -- constructor; [| constructor; [|constructor]]; cbn [w_kind w_iv w_lo w_len]; intros _; left; (split; [left; reflexivity|]); intros b Hb a Ha Hb'; apply in_map_iff in Hb as (c & <- & Hc).
           ++ pose proof (UO.disj_cc g LB O c Hc) as D. unfold rdisj, in_iv, chunk_block, w_iv in D, Ha, Hb'. cbn [fst snd w_lo w_len] in D, Ha, Hb'. lia.
           ++ pose proof (UO.disj_vc g LB O c Hc) as D. unfold rdisj, in_iv, chunk_block, w_iv in D, Ha, Hb'. cbn [fst snd w_lo w_len] in D, Ha, Hb'. lia.
      *
        split; [| split].
        3: {
             apply (PkUAdd.add_cost _ _ _ g' [] NOUw). intros x fr v Hx PX. subst uw. destruct sc as [lo|]; [| destruct Hx]. destruct Hx as [<-|[]].
             destruct (UVAL lo eq_refl) as (U1 & U2 & _). rewrite (PkU.mk_pku_val E false n ltac:(rewrite U1; exact U2)) in PX. injection PX as <- <-.
             change (k_tree g') with t. cbn [np]. rewrite U1, (PkCost.pk10_tree_split t). pose proof (PkCost.own10_nonneg _ _ t TWt). lia. }
        2: { apply (PkUAdd.add_ghost _ _ PU). split.
             - change (k_zone g') with (u_zone g). rewrite WS'. apply Seal.seal_ok_app; [exact KSEALu|]. constructor; [cbn [w_kind]; unfold K_BLOCK, Seal.K_TWIN; lia| constructor; [cbn [w_kind]; unfold K_BLOCK, Seal.K_TWIN; lia| constructor]].
             - intros X. exfalso. apply X. reflexivity. }
        unfold mem_pk. change (k_tree g') with t. change (k_zone g') with (u_zone g). change (k_evec g') with (mkVec 0 0 0 ELEM_SIZE).
        cbn [a_root v_begin]. rewrite <- Lroot.
        split; [exact TWt|]. split; [exact KAt|]. split; [| split; [destruct M as (_ & _ & _ & CH & _); exact CH| intros X; exfalso; exact (X eq_refl)]].
        split.
        -- intros c Hc. destruct (TLC c Hc) as [IA _]. exact (body_in_zone _ _ _ ZV IA).
        -- unfold bodies_ok in BOD. apply Forall_forall. intros b Hb. pose proof (proj1 (Forall_forall _ _) BOD b Hb) as (R1 & R2 & _).
           split; [exact R1| exact (body_in_zone _ _ _ ZV R2)].
  -   intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E) (ws' ++ uw)) _ a (mk_args_sound E 3%uint63 aw (ws' ++ uw) _ LENn))) in FPa as (RA & NI & NWn).
    assert (NW : ~ in_ws (map (wden E) ws') a) by (intros X; apply NWn; rewrite map_app; apply (PkUAdd.add_in_ws _ _ PU a); exact X).
    rewrite WS' in NW. split.
    + destruct (in_ws_dec (map (wden E) ws) a) as [IW|NWo]; [| left; exact (FPold a RA NI NWo)].
      apply (proj1 (in_ws_map_iff E ws a)) in IW as (w3 & Hw3 & Hin).
      destruct (is_kept w3) eqn:IK.
      * exfalso. destruct (DOLD w3 Hw3) as [Hw0|PS]; [| exact (PotDrop.pseudo_no_byte _ a PS Hin)].
        apply NW. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). left.
        apply in_ivs_In. exists (w_iv (wden E w3)). split; [| exact Hin]. apply in_map. apply in_map. apply filter_In. auto.
      * right. exact (SUBR w3 a Hw3 (kept_or_sub ws w3 KL Hw3 IK) Hin).
    + intros k r [X|[X|[]]] IR; injection X as <- <-; unfold inR in IR; rewrite LOE in IR; apply NW; unfold in_ws; rewrite map_app;
        apply (proj2 (in_ivs_app _ _ _)); right; cbn [map]; unfold in_ivs.
      * rewrite HIC, CBV in IR. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. lia.
      * rewrite HIV, VBV in IR. apply Exists_cons_tl. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. lia.
  -
    assert (ZB : forall p sz, in_zone (u_zone g) p sz -> 0 <= sz -> 4104 <= p /\ p + sz <= 4611686018427387904).
    { intros p sz (ch' & Hch' & ICH') Hsz.
      pose proof (proj1 O _ (UO.owned_chunk g ch' Hch')) as INB.
      destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch') HA INB) as (Bd1 & Bd2 & Bd3 & Bd4 & Bd5).
      pose proof (aw_blocks_lo segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch') HA INB) as BLO.
      unfold chunk_block in Bd1, Bd2, Bd3, BLO. cbn [fst snd] in Bd1, Bd2, Bd3, BLO.
      unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICH'. unfold CHUNK_HDR in *. lia. }
    destruct (KF.kids_pure _ _ _ TWt ZB) as (KP1 & KP2 & KP3 & KP4).
    match goal with |- Forall _ ?l => change l with (KF.kids_facts n1 P1 ++ uf) end.
    apply Forall_app. split; [exact (KF.kids_facts_sound E n1 P1 _ _ (eq_sym RN) (eq_sym RP) KP1 KP2 KP3 KP4)|].

    subst uf. destruct sc as [lo|]; [| constructor]. destruct (UVAL lo eq_refl) as (U1 & U2 & U3).
    constructor; [| constructor; [| constructor]].
    + cbn [fact_holds]. apply bv_eq. rewrite U3.
      remember (VAlu ALU_SLL (VP n wzero) (VL GPot.wtwo)) as sl eqn:SL. cbn [den]. rewrite GPot.alu_add_u, wbv_unsigned. subst sl.
      rewrite GPot.alu_sll2_u, (den_VP0 E n wzero (weqb_refl _)), U1.
      change (w2Z HANDW) with (POT_BASE + Pot.Pot.Q0). pose proof (PkCost.pk10_tree_nonneg _ _ t TWt) as NN.
      assert (Q : POT_BASE + Pot.Pot.Q0 = 6917529027775299584) by reflexivity.
      rewrite (Z.mod_small (PK.pk10_tree t * 4)) by (unfold two64; lia). rewrite Z.mod_small by (unfold two64; lia). lia.
    + cbn [fact_holds]. rewrite U1. change (w2Z wzero) with 0. change (w2Z PkU.UMAX) with (2 ^ 41). pose proof (PkCost.pk10_tree_nonneg _ _ t TWt). lia.
Qed.

Lemma pkenter_inv : forall st st', pkenter_apply st = Some [st'] ->
  exists md aw ws ca sc, the_op st = Some (md, aw, ws, ca) /\ GPot.pot_scan (s_facts st) ws = Some sc /\
    st_vars_below (s_next st) st = true /\ 0 < to_Z (s_next st) /\ match sc with Some lo => sv_vars_below (s_next st) lo = true | None => True end.
Proof.
  intros st st' AP. unfold pkenter_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 2); [|discriminate].
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbv zeta in AP.
  destruct cb as [|kCB oCB| | | | | | | | |]; try discriminate.
  destruct vb as [|kVB oVB| | | | | | | | |]; try discriminate.
  destruct zh as [|kZ oZ| | | | | | | | |]; try discriminate.
  destruct (cap_len kCB ccap) as [lenC|]; [|discriminate].
  destruct (cap_len kVB vcap) as [lenV|]; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  do 10 (apply andb_prop in COND as [COND _]).
  unfold common_ok in COND. apply andb_prop in COND as [COND _]. apply andb_prop in COND as [COND _]. apply andb_prop in COND as [VB NPOS].
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS.
  destruct (sub_anchors st ws); [|discriminate]. destruct (IMap.find kZ (s_regs st)); [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  destruct (GPot.pot_scan (s_facts st) ws) as [sc|] eqn:PSC; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND3; [|discriminate] end.
  apply andb_prop in COND3 as [VBLO _].
  eexists _, _, _, _, sc. split; [reflexivity|]. split; [exact PSC|]. split; [exact VB|]. split; [exact NPOS|].
  destruct sc; [exact VBLO| exact I].
Qed.

Theorem pkenter_sound : forall pc, contract_sound segs OPS MP PB (pkenter_contract pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [pkenter_contract c_apply] in HAP.
  destruct (pkenter_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  2: { injection HAP as <-.
       destruct (pkenter_inv st st' AP) as (md0 & aw0 & ws0 & ca0 & sc & TO & PSC & VB & NPOS & VLO).
       set (n := s_next st) in *.
       set (E' := match sc with Some lo => env_upd E n (Z_to_bv 64 ((bv_unsigned (den E lo) - POT_BASE - Pot.Pot.Q0) / 4)) | None => E end).
       assert (HX : env_ext n E E') by (subst E'; destruct sc; [apply env_upd_ext| apply env_ext_refl]).
       assert (HS' : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS).
       apply (Hk st' (or_introl eq_refl) E' ms model HX HMP).
       apply (pkenter_sound_main E' st ms model st' HS' AP).
       intros md1 aw1 ws1 ca1 lo TO1 PSC1. rewrite TO in TO1. injection TO1 as <- <- <- <-. rewrite PSC in PSC1. injection PSC1 as ->.
       fold n. subst E'. cbn beta iota. rewrite (den_reval n E _ (env_upd_ext _ _ _) lo VLO). apply env_upd_same. }
  all: exfalso; unfold pkenter_apply in AP;
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End PkEnter.
