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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Ops GLib GUnp U32.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Pot GPot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import LiaFast.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU U32.
Open Scope Z_scope.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module G3.

Definition no_slot_windows (ws : list (sv * sv * sv)) : bool :=
  forallb (fun w => match kind_of w with Some kd => negb (kd =? K_SLOT) | None => false end) ws.

Definition slot_win (kS : int) : sv * sv * sv := (VP kS wzero, VL (wlit 24%uint63), VL (wlit 4%uint63)).
Definition empty_slot_region : region := Region 0%uint63 (VL (wlit 24%uint63)) true BGNone IMap.empty.
Definition set_levels (g : unpg) (ls : list level) : unpg :=
  mkUnp (u_ctx g) (u_vis g) (u_data g) (u_len g) ls (u_cstk g) (u_vstk g) (u_zone g).

Lemma no_slot_windows_sound : forall E ws, no_slot_windows ws = true ->
  forall w, In w (map (wden E) ws) -> w_kind w <> K_SLOT.
Proof.
  intros E ws H w Hw. apply in_map_iff in Hw as (x & <- & Hx).
  pose proof (proj1 (forallb_forall _ _) H x Hx) as Q. cbn beta in Q.
  destruct (kind_of x) as [kd|] eqn:KD; [|discriminate]. rewrite (kind_of_sound E x kd KD).
  destruct (Z.eqb_spec kd K_SLOT); [discriminate| assumption].
Qed.

Lemma slot_win_den : forall E kS, wden E (slot_win kS) = Win (bv_unsigned (ev E kS)) 24 K_SLOT.
Proof.
  intros E kS. unfold slot_win, wden. rewrite (den_VP0 E kS wzero (weqb_refl _)). cbn [den]. rewrite !wbv_unsigned, !wlit_ok. reflexivity.
Qed.

Lemma vars_below_find_none_ge : forall n k st, IMap.bst (s_regs st) -> st_vars_below n st = true -> to_Z n <= to_Z k ->
  IMap.find k (s_regs st) = None.
Proof.
  intros n k st B H LE. unfold st_vars_below in H.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [_ H].
  destruct (IMap.find k (s_regs st)) as [r|] eqn:F; [|reflexivity].
  pose proof (proj1 (IMap.forallb_spec _ _ B) H k r F) as Q. apply andb_prop in Q as [Q _].
  apply Uint63.ltb_spec in Q. lia.
Qed.
Lemma vars_below_find_none : forall n st, IMap.bst (s_regs st) -> st_vars_below n st = true -> IMap.find n (s_regs st) = None.
Proof. intros n st B H. apply (vars_below_find_none_ge n n st B H). lia. Qed.

Lemma conts_at_tl_last : forall m root ls l l',
  container_type (lv_t l') = container_type (lv_t l) -> lv_n l' = lv_n l -> lv_P l' = lv_P l ->
  conts_at m (tl (containers root (ls ++ [l]))) (tl (ls ++ [l])) ->
  conts_at m (tl (containers root (ls ++ [l']))) (tl (ls ++ [l'])).
Proof.
  intros m root ls l l' ET EN EP H. destruct ls as [|l0 ls0]; cbn [app containers tl] in *; [exact I|].
  rewrite containers_app in H |- *. cbn [containers] in H |- *.
  apply (proj1 (conts_at_app m _ _ ls0 [l] (containers_length _ _))) in H as [H1 H2].
  apply (proj2 (conts_at_app m _ _ ls0 [l'] (containers_length _ _))). split; [exact H1|].
  cbn [conts_at] in H2 |- *. rewrite ET, EN, EP. exact H2.
Qed.

Definition is_decr (fs : list fact) (rc restD : sv) : bool :=
  (sv_eqb (sv_alu ALU_ADD rc (VL wone)) restD
   || msame restD (VAlu ALU_ADD rc (VL wone))
   || (same32 rc (VAlu ALU_ADD restD (VL wones)) && sx32_shaped rc))
  && match decide_eq0 fs rc with Some false => true | _ => false end.

Definition ret_case (fs : list fact) (tD restD tc rc : sv) : option Z :=
  if match decide_eq fs tD (VL wzero) with Some true => true | _ => false end then
    (if sv_eqb tc tD && is_decr fs rc restD then Some 0 else None)
  else if match decide_eq fs tD (VL wone) with Some true => true | _ => false end then
    (if sv_eqb tc (VL (wlit 2%uint63)) && sv_eqb rc restD then Some 1 else None)
  else if match decide_eq fs tD (VL (wlit 2%uint63)) with Some true => true | _ => false end then
    (if sv_eqb tc (VL wone) && is_decr fs rc restD then Some 2 else None)
  else None.

Section WithPc.
Variable RET_PC : int.

Definition SLOT_HI : w64 := wlit 4611686018427387904%uint63.

Definition g3r_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 2%uint63 then
      match ca with
      | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
          match slot, ce, ve with
          | VP kS os, VP kCT oce, VP kVT ove =>
              let n := s_next st in
              if weqb os wzero && weqb oce (wlit 8%uint63) && weqb ove (wlit 8%uint63)
                 && negb (PrimInt63.eqb kS 0%uint63) && negb (PrimInt63.eqb kCT 0%uint63) && negb (PrimInt63.eqb kVT 0%uint63)
                 && no_slot_windows ws && st_vars_below n st && PrimInt63.ltb 0%uint63 n && Z.ltb (Z.of_nat (length ws)) 4096
                 && match decide_ltu (s_facts st) cb (VP kCT oce) with Some true => true | _ => false end
              then
                match IMap.find kCT (s_regs st), IMap.find kVT (s_regs st) with
                | Some rc, Some rv =>
                    match cell_at rv 0 8%uint63, cell_at rc 0 4%uint63, cell_at rc 4 4%uint63 with
                    | Some sp, Some tc, Some rcl =>
                        if sv_eqb sp (VP kS (wlit 24%uint63)) then
                          match ret_case (s_facts st) tD restD tc rcl with
                          | Some _ =>
                              match GPot.GPot.pot_scan_c (s_facts st) aw ws with
                              | Some sc =>
                              let ca' := [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; VP n wzero; tc; rcl; rootT; n1; P1; zh] in
                              let ws' := GPot.GPot.pot_lit sc GPot.GPot.D_RETw (ws ++ [slot_win n]) in
                              Some [surg st [] [(n, empty_slot_region)] (mk_args 1%uint63 aw ws' ca')
                                         [FEq (VP n wzero) (VP kS (wlit 24%uint63)); FRange n (wlit 24%uint63) SLOT_HI; FAlign n 3%uint63] (PrimInt63.add n 1%uint63)]
                              | None => None
                              end
                          | None => None
                          end
                        else None
                    | _, _, _ => None
                    end
                | _, _ => None
                end
              else None
          | _, _, _ => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Definition g3r_contract : contract := Contract RET_PC g3r_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma is_decr_sound : forall E fs rc restD, facts_hold E fs -> ev E 0%uint63 = Z_to_bv 64 0 ->
  is_decr fs rc restD = true -> 1 <= bv_unsigned (den E restD) -> bv_unsigned (den E restD) <= LIMIT ->
  bv_unsigned (den E rc) = bv_unsigned (den E restD) - 1 /\ 2 <= bv_unsigned (den E restD).
Proof.
  intros E fs rc restD FH Z0 H R1 RL. unfold is_decr in H. apply andb_prop in H as [H1 H2].
  destruct (decide_eq0 fs rc) as [[|]|] eqn:D; try discriminate.
  pose proof (decide_eq0_sound E fs FH rc false D) as NZ0. apply (proj1 (eqb_iff _ _ false)) in NZ0.
  assert (NZ0' : bv_unsigned (den E rc) <> 0).
  { intros X. apply NZ0. apply bv_eq. rewrite X. rewrite Z_to_bv_unsigned. reflexivity. }
  apply orb_prop in H1 as [H1|H3].
  2:{
      apply andb_prop in H3 as [S32 SX].
      pose proof (same32_sound E _ _ S32) as M. pose proof (sx32_shaped_sound E _ SX) as P.
      pose proof (bv_unsigned_in_range _ (den E rc)) as Rr. rewrite bv_modulus_64 in Rr.
      pose proof (bv_unsigned_in_range _ (den E restD)) as Rd. rewrite bv_modulus_64 in Rd.
      assert (M2 : bv_unsigned (den E (VAlu ALU_ADD restD (VL wones))) mod 2 ^ 32 = bv_unsigned (den E restD) - 1).
      { change (den E (VAlu ALU_ADD restD (VL wones))) with (alu64 ALU_ADD (den E restD) (den E (VL wones))). cbn [alu64 alu den].
        rewrite bv_add_unsigned, wbv_unsigned. change (w2Z wones) with (two64 - 1). unfold bv_wrap. rewrite bv_modulus_64.
        replace (bv_unsigned (den E restD) + (two64 - 1)) with ((bv_unsigned (den E restD) - 1) + 1 * two64) by (clear; lia).
        rewrite Z_mod_plus_full. rewrite (Z.mod_small _ two64) by (unfold LIMIT, two64 in *; lia). apply Z.mod_small. unfold LIMIT in *; lia. }
      rewrite M2 in M. unfold two64 in Rr.
      pose proof (sxP_low31 (bv_unsigned (den E rc)) Rr P ltac:(rewrite M; unfold LIMIT in *; lia)) as EQ. rewrite M in EQ.
      split; [exact EQ|]. unfold LIMIT in *. lia. }
  assert (A : den E restD = alu64 ALU_ADD (den E rc) (den E (VL wone))).
  { apply orb_prop in H1 as [H1|H1].
    - apply sv_eqb_eq in H1. pose proof (den_sv_alu E ALU_ADD rc (VL wone)) as A. rewrite H1 in A. exact A.
    - exact (msame_sound E _ _ H1). }
  pose proof (decide_eq0_sound E fs FH rc false D) as NZ. apply (proj1 (eqb_iff _ _ false)) in NZ.
  pose proof (bv_unsigned_in_range _ (den E rc)) as Rr. pose proof (bv_unsigned_in_range _ (den E restD)) as Rd.
  rewrite bv_modulus_64 in Rr, Rd.
  assert (U : bv_unsigned (den E restD) = (bv_unsigned (den E rc) + 1) mod two64).
  { rewrite A. cbn [alu64 alu den]. rewrite bv_add_unsigned, wbv_unsigned, wone_ok. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. }
  assert (NZ' : bv_unsigned (den E rc) <> 0).
  { intros X. apply NZ. apply bv_eq. rewrite X. rewrite Z_to_bv_unsigned. reflexivity. }
  destruct (Z.eq_dec (bv_unsigned (den E rc) + 1) two64) as [EQ|NE].
  - rewrite EQ, Z.mod_same in U by (unfold two64; lia). lia.
  - rewrite Z.mod_small in U by lia. lia.
Qed.

Lemma g3r_apply_sound : forall E st ms model st',
  st_ok segs OPS E st ms model -> g3r_apply st = Some [st'] ->
  exists E', env_ext (s_next st) E E' /\ st_ok segs OPS E' st' ms model.
Proof.
  intros E st ms model st' HS0 AP.
  unfold g3r_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 2) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct slot as [|kS os| | | | | | | | |]; try discriminate.
  destruct ce as [|kCT oce| | | | | | | | |]; try discriminate.
  destruct ve as [|kVT ove| | | | | | | | |]; try discriminate.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  destruct (IMap.find kCT (s_regs st)) as [rc|] eqn:FC; [|discriminate].
  destruct (IMap.find kVT (s_regs st)) as [rv|] eqn:FV; [|discriminate].
  destruct (cell_at rv 0 8%uint63) as [sp|] eqn:CSP; [|discriminate].
  destruct (cell_at rc 0 4%uint63) as [tc|] eqn:CTC; [|discriminate].
  destruct (cell_at rc 4 4%uint63) as [rcl|] eqn:CRC; [|discriminate].
  destruct (sv_eqb sp (VP kS (wlit 24))) eqn:SP; [|discriminate]. apply sv_eqb_eq in SP. subst sp.
  destruct (ret_case (s_facts st) tD restD tc rcl) as [cs|] eqn:RC; [|discriminate].
  destruct (GPot.GPot.pot_scan_c (s_facts st) aw ws) as [sc|] eqn:SCAN; [|discriminate].
  injection AP as <-.
  apply andb_prop in COND as [COND DLT].
  apply andb_prop in COND as [COND WLEN]. apply Z.ltb_lt in WLEN.
  apply andb_prop in COND as [COND NPOS]. apply andb_prop in COND as [COND VB]. apply andb_prop in COND as [COND NSW].
  apply andb_prop in COND as [COND KVT0]. apply andb_prop in COND as [COND KCT0]. apply andb_prop in COND as [COND KS0].
  apply andb_prop in COND as [COND OVE]. apply andb_prop in COND as [OS OCE].
  apply (proj1 (weqb_ok _ _)) in OS. apply (proj1 (weqb_ok _ _)) in OCE. apply (proj1 (weqb_ok _ _)) in OVE. subst os oce ove.
  apply negb_true_iff in KS0. apply negb_true_iff in KCT0. apply negb_true_iff in KVT0.
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS.
  set (n := s_next st) in *.

  set (E' := env_upd E n (bv_add (ev E kS) (wbv (wlit 24%uint63)))).
  assert (HX : env_ext n E E') by apply env_upd_ext.
  exists E'. split; [exact HX|].
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
  clear HS0.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].

  destruct (the_op_full st 2%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  assert (INCA : forall v, In v [root; cb; VP kCT (wlit 8); ccap; vb; VP kVT (wlit 8); vcap; zptr; zfree; c0; VP kS wzero; tD; restD; rootT; n1; P1; zh] ->
                           In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  pose proof (ops_vars_below n st o VB (op_in_In st o OPS1)) as VBo.
  assert (KSn : PrimInt63.ltb kS n = true) by exact (VBo (VP kS wzero) (INCA (VP kS wzero) ltac:(do 10 right; left; reflexivity))).
  assert (EVkS : ev E' kS = ev E kS) by exact (ev_reval n E E' HX kS KSn).
  assert (EVn : ev E' n = bv_add (ev E' kS) (wbv (wlit 24%uint63))) by (rewrite EVkS; apply env_upd_same).
  clearbody E'.

  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E') as DEC.
  rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 2%uint63) with 2 in HC.
  cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC.
  cbn [map decode_uc] in HC.
  destruct HC as (g & L & P & O & Wk & M & CS0 & AX & SE).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap, Lzp, Lzf, Lc0, LD.
  pose proof (pf g P) as (VC & EC & SC & VV & EV & SV' & LV & LA & ZV).
  destruct M as (M1 & M2 & M3 & M4 & M5 & M6).
  destruct (CS0 eq_refl) as (o0 & TW0 & KA0 & HD0 & _ & TLC & BOD & DEP0 & PT0).
  pose proof (GPot.GPot.pot_scan_c_ok E' (s_facts st) aw ws sc Pfacts SCAN) as SCOK.

  assert (NE : u_levels g <> []).
  { destruct (decide_ltu (s_facts st) cb (VP kCT (wlit 8))) as [[|]|] eqn:DL; try discriminate.
    pose proof (decide_ltu_sound E' (s_facts st) Pfacts _ _ _ DL) as LT. apply (proj1 (ltu_iff _ _ true)) in LT.
    cbn [den] in LT, Lcb, Lce. rewrite <- Lcb, <- Lce in LT. unfold v_end in LT. rewrite EC, SC in LT.
    intros X. unfold u_D in LT. rewrite X in LT. cbn [length Z.of_nat] in LT. lia. }
  assert (TREE : tree_at (bmem_of segs (ms_mem ms)) (u_zone g) (u_cur_slot g) o0).
  { split; [| exact TW0]. apply (proj2 (obj_at_split _ _ _)). split; [exact (HD0 NE)| exact KA0]. }
  destruct (LD NE) as (Lslot & (lD & HlD & LtD & LrD) & (l1 & ls1 & E1 & LT1 & LN1 & LP1)).
  cbn [c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lslot, LtD, LrD, LT1, LN1, LP1.

  destruct (exists_last NE) as (ls & l & ELS).
  assert (HlD' : lD = l).
  { rewrite ELS in HlD. unfold last_opt in HlD. rewrite rev_app_distr in HlD. cbn in HlD. congruence. }
  subst lD.
  assert (Vl : level_valid l) by (apply (proj1 (Forall_forall _ _) LV); rewrite ELS; apply in_app_iff; right; left; reflexivity).
  assert (SLOT : u_cur_slot g = lv_slot l) by (unfold u_cur_slot; rewrite ELS; apply cur_slot_snoc).
  assert (KSV : bv_unsigned (ev E' kS) = lv_slot l).
  { rewrite <- SLOT, Lslot. symmetry. exact (den_VP0 E' kS wzero (weqb_refl _)). }

  pose proof Vl as (VR1 & VR2 & VR3 & VR4 & VR5).
  assert (TCODE : forall w, decide_eq (s_facts st) tD (VL w) = Some true -> ctype_code (lv_t l) = w2Z w).
  { intros w Hd. pose proof (decide_eq_sound E' (s_facts st) Pfacts tD (VL w) true Hd) as Q.
    apply (proj1 (eqb_iff _ _ true)) in Q. rewrite LtD, Q. cbn [den]. apply wbv_unsigned. }
  assert (CASE0 : decide_eq (s_facts st) tD (VL wzero) = Some true -> sv_eqb tc tD && is_decr (s_facts st) rcl restD = true ->
            exists l', consume_top l = CS_Ret l' /\ ctype_code (lv_t l') = bv_unsigned (den E' tc) /\ lv_rest l' = bv_unsigned (den E' rcl)).
  { intros D0 C. apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. subst tc.
    destruct (is_decr_sound E' (s_facts st) rcl restD Pfacts Pz C2 ltac:(rewrite <- LrD; lia) ltac:(rewrite <- LrD; unfold LIMIT in *; lia)) as [DR R2].
    pose proof (TCODE wzero D0) as T0. rewrite wzero_ok in T0.
    assert (LT : lv_t l = CT_ARRAY_ITEM) by (destruct (lv_t l); cbn in T0; try reflexivity; lia).
    exists (mkLevel CT_ARRAY_ITEM (lv_n l) (lv_rest l - 1) (lv_P l)).
    unfold consume_top. rewrite LT. destruct (Z.eqb_spec (lv_rest l) 1); [lia|].
    split; [reflexivity|]. cbn [lv_t lv_rest ctype_code]. split; [rewrite <- T0; exact LtD| lia]. }
  assert (CASE1 : decide_eq (s_facts st) tD (VL wone) = Some true -> sv_eqb tc (VL (wlit 2%uint63)) && sv_eqb rcl restD = true ->
            exists l', consume_top l = CS_Ret l' /\ ctype_code (lv_t l') = bv_unsigned (den E' tc) /\ lv_rest l' = bv_unsigned (den E' rcl)).
  { intros D1 C. apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. apply sv_eqb_eq in C2. subst tc rcl.
    pose proof (TCODE wone D1) as T1. rewrite wone_ok in T1.
    assert (LT : lv_t l = CT_MAP_KEY) by (destruct (lv_t l); cbn in T1; try reflexivity; lia).
    exists (mkLevel CT_MAP_VALUE (lv_n l) (lv_rest l) (lv_P l)).
    unfold consume_top. rewrite LT. split; [reflexivity|]. cbn [lv_t lv_rest ctype_code den].
    rewrite wbv_unsigned, wlit_ok. split; [reflexivity| exact LrD]. }
  assert (CASE2 : decide_eq (s_facts st) tD (VL (wlit 2%uint63)) = Some true -> sv_eqb tc (VL wone) && is_decr (s_facts st) rcl restD = true ->
            exists l', consume_top l = CS_Ret l' /\ ctype_code (lv_t l') = bv_unsigned (den E' tc) /\ lv_rest l' = bv_unsigned (den E' rcl)).
  { intros D2 C. apply andb_prop in C as [C1 C2]. apply sv_eqb_eq in C1. subst tc.
    destruct (is_decr_sound E' (s_facts st) rcl restD Pfacts Pz C2 ltac:(rewrite <- LrD; lia) ltac:(rewrite <- LrD; unfold LIMIT in *; lia)) as [DR R2].
    pose proof (TCODE (wlit 2%uint63) D2) as T2. rewrite wlit_ok in T2. change (to_Z 2%uint63) with 2 in T2.
    assert (LT : lv_t l = CT_MAP_VALUE) by (destruct (lv_t l); cbn in T2; try reflexivity; lia).
    exists (mkLevel CT_MAP_KEY (lv_n l) (lv_rest l - 1) (lv_P l)).
    unfold consume_top. rewrite LT. destruct (Z.eqb_spec (lv_rest l) 1); [lia|].
    split; [reflexivity|]. cbn [lv_t lv_rest ctype_code den]. rewrite wbv_unsigned, wone_ok. split; [reflexivity| lia]. }
  assert (CASE : exists l', consume_top l = CS_Ret l' /\ ctype_code (lv_t l') = bv_unsigned (den E' tc) /\ lv_rest l' = bv_unsigned (den E' rcl)).
  { unfold ret_case in RC.
    destruct (decide_eq (s_facts st) tD (VL wzero)) as [[|]|] eqn:D0.
    1: { destruct (sv_eqb tc tD && is_decr (s_facts st) rcl restD) eqn:C; [exact (CASE0 eq_refl eq_refl)| discriminate]. }
    all: destruct (decide_eq (s_facts st) tD (VL wone)) as [[|]|] eqn:D1.
    1,4: destruct (sv_eqb tc (VL (wlit 2)) && sv_eqb rcl restD) eqn:C; [exact (CASE1 eq_refl eq_refl)| discriminate].
    all: destruct (decide_eq (s_facts st) tD (VL (wlit 2))) as [[|]|] eqn:D2; try discriminate.
    all: destruct (sv_eqb tc (VL wone) && is_decr (s_facts st) rcl restD) eqn:C; [exact (CASE2 eq_refl eq_refl)| discriminate]. }
  clear CASE0 CASE1 CASE2.
  destruct CASE as (l' & CT & TC' & RC').
  pose proof (consume_top_ret l l' CT Vl) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  pose proof (level_geom l Vl) as GE. pose proof (level_geom l' S5) as GE'. assert (HO : OBJ_SIZE = 24) by reflexivity.
  set (g' := set_levels g (ls ++ [l'])).

  assert (INl : In l (u_levels g)) by (rewrite ELS; apply in_app_iff; right; left; reflexivity).
  destruct (level_block g LB l P O INl) as (ch & Hch & OWN & INB).
  pose proof (no_slot_windows_sound E' ws NSW) as N4.
  assert (BYTE : forall a, lv_P l <= a < lv_P l + lv_bytes l ->
            (0 <= a /\ a + 1 < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws (map (wden E') ws) a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (owned_byte_props segs IMGX AW _ LB (ms_mem ms) model 2 g (map (wden E') ws) (chunk_block ch) a HA WF O Wk OWN (INB a Ha)).
    exact (safe_level_no4 2 g LB (map (wden E') ws) l a P O N4 INl Ha). }

  assert (NEWSLOT : lv_P l <= lv_slot l' /\ lv_slot l' + 24 <= lv_P l + lv_bytes l) by (rewrite <- S2, <- S6; unfold OBJ_SIZE in GE'; lia).
  assert (BASE : bv_unsigned (ev E' n) = lv_slot l').
  { rewrite EVn, bv_add_unsigned, wbv_unsigned, wlit_ok, KSV. change (to_Z 24%uint63) with 24. rewrite S1, HO.
    unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small.
    destruct (BYTE (lv_slot l + 23) ltac:(lia)) as (R & _). lia. }
  assert (HIZ : hiZ E' empty_slot_region = 24).
  { unfold hiZ, empty_slot_region. cbn [rg_hi den]. rewrite wbv_unsigned, wlit_ok. reflexivity. }
  assert (LOZ : loZ empty_slot_region = 0) by reflexivity.
  assert (LEN' : Z.of_nat (length (GPot.GPot.pot_lit sc GPot.GPot.D_RETw (ws ++ [slot_win n]))) < two63).
  { rewrite GPot.GPot.pot_lit_length, length_app. cbn [length]. unfold two63. lia. }
  assert (DRET : 0 <= w2Z GPot.GPot.D_RETw <= 2 ^ 20) by (change (w2Z GPot.GPot.D_RETw) with 48; lia).
  pose proof (GPot.GPot.scan_oldb E' ws sc SCOK) as OLDB. pose proof (GPot.GPot.lit_newb E' ws sc GPot.GPot.D_RETw SCOK DRET) as NEWB.

  apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [] [(n, empty_slot_region)] (mk_args 1%uint63 aw (GPot.GPot.pot_lit sc GPot.GPot.D_RETw (ws ++ [slot_win n])) _) _ (PrimInt63.add n 1)).
  - intros k [].
  - constructor; [intros []| constructor].
  - intros k r [H|[]]. injection H as <- <-.
    apply (proj2 (Uint63.eqb_false_spec _ _)). intros X. rewrite X in NPOS. change (to_Z 0%uint63) with 0 in NPOS. lia.
  -
    intros k r [H|[]]. injection H as <- <-.
    apply (region_ok_fresh segs (s_priv st) E' (ms_mem ms) n empty_slot_region).
    + apply (proj2 (Uint63.eqb_false_spec _ _)). intros X. rewrite X in NPOS. change (to_Z 0%uint63) with 0 in NPOS. lia.
    + exact I.
    + reflexivity.
    + rewrite BASE, LOZ. destruct (BYTE (lv_slot l') ltac:(lia)) as (R & _). lia.
    + rewrite BASE, HIZ. destruct (BYTE (lv_slot l' + 23) ltac:(lia)) as (R & _). lia.
    + intros a Ha. rewrite BASE, LOZ, HIZ in Ha. destruct (BYTE a ltac:(lia)) as (_ & _ & _ & MT & NSG). auto.
    + intros gk gr F. cbn [empty_slot_region rg_cells] in F. rewrite IMap.find_empty in F. discriminate.
  -
    intros k r a [H|[]] IR. injection H as <- <-. unfold inR in IR. rewrite BASE, LOZ, HIZ in IR.
    destruct (BYTE a ltac:(lia)) as (RA & NI & NW & _).
    left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS).
    apply (proj2 (heap_fp_iff IMGX _ 2 _ (map (wden E') ws) _ a DEC)). split; [lia| auto].
  - intros k1 r1 k2 r2 a [H1|[]] [H2|[]] NE12. injection H1 as <- <-. injection H2 as <- <-. contradiction.
  -
    rewrite (ho_holds _ _ _ _ _ HOPS).
    exists 1, (den E' aw), (map (wden E') (GPot.GPot.pot_lit sc GPot.GPot.D_RETw (ws ++ [slot_win n]))), (map (den E') [root; cb; VP kCT (wlit 8); ccap; vb; VP kVT (wlit 8); vcap; zptr; zfree; c0; VP n wzero; tc; rcl; rootT; n1; P1; zh]), LB.
    split; [apply mk_args_sound; exact LEN'|].
    split; [apply (aw_keep segs IMGX AW _ _ (map (wden E') (ws ++ [slot_win n])));
            [apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); rewrite map_app; apply wins_keep_app; intros w0 [<-|[]]; apply UOK.kind_sub_untied; vm_compute; reflexivity
            | exact (GPot.GPot.wins_keep_pot_set E' sc _ _ OLDB NEWB LB)]|]. split.
    +
      apply (GPot.GPot.windows_wf_pot_set E' sc _ _ OLDB NEWB LB _ (aw_ceiling_small segs IMGX AW model)).
      unfold windows_wf in *. rewrite map_app. apply Forall_app. split; [exact WF|]. constructor; [|constructor].
      rewrite slot_win_den, BASE. unfold window_wf. cbn [w_lo w_len w_kind w_iv].
      destruct (BYTE (lv_slot l') ltac:(lia)) as (R0 & _).
      split; [lia|]. split; [lia|]. split; [destruct (BYTE (lv_slot l' + 23) ltac:(lia)) as (R & _); lia|].
      right; right. split; [unfold K_SUB, K_SLOT; lia|]. exists (chunk_block ch). split; [exact (proj1 O _ OWN)|].
      intros a Ha. apply INB. unfold in_iv, w_iv in Ha. cbn [fst snd w_lo w_len] in Ha. lia.
    +
      cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. cbn [map decode_uc].
      exists g'.
      assert (UL : u_levels g' = ls ++ [l']) by reflexivity.
      assert (UD : u_D g' = u_D g) by (unfold u_D; rewrite UL, ELS, !length_app; reflexivity).
      assert (SUBL : forall x', In x' (ls ++ [l']) -> exists x, In x (u_levels g) /\ lv_slot x <= lv_slot x' /\ lv_slot x' + lv_unfilled x' <= lv_slot x + lv_unfilled x).
      { intros x' Hx'. rewrite ELS. apply in_app_iff in Hx'. destruct Hx' as [Hx'|[<-|[]]].
        - exists x'. split; [apply in_app_iff; now left|lia].
        - exists l. split; [apply in_app_iff; right; now left|]. lia. }
      split; [| split; [| split; [| split; [| split; [| split]]]]].
      *
        unfold link. cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1].
        change (u_root g') with (u_root g). change (u_cstk g') with (u_cstk g). change (u_vstk g') with (u_vstk g). change (u_zone g') with (u_zone g).
        rewrite UL.
        split; [exact Lroot|]. split; [exact Lcb|]. split; [exact Lce|]. split; [exact Lccap|]. split; [exact Lvb|]. split; [exact Lve|].
        split; [exact Lvcap|]. split; [exact Lzp|]. split; [exact Lzf|]. split; [exact Lc0|].
        intros _. split; [| split].
        -- change (u_cur_slot g') with (cur_slot (u_root g) (ls ++ [l'])). rewrite cur_slot_snoc.
           rewrite (den_VP0 E' n wzero (weqb_refl _)), BASE. reflexivity.
        -- exists l'. split; [unfold last_opt; rewrite rev_app_distr; reflexivity|]. split; [exact TC'| exact RC'].
        -- destruct ls as [|l0 ls0].
           ++ exists l', []. split; [reflexivity|]. cbn [app] in ELS. rewrite ELS in E1. injection E1 as <- <-.
              rewrite S7, S3, S2. auto.
           ++ exists l0, (ls0 ++ [l']). split; [reflexivity|]. rewrite ELS in E1. cbn [app] in E1. injection E1 as <- <-. auto.
      *
        unfold pure_ok. change (u_cstk g') with (u_cstk g). change (u_vstk g') with (u_vstk g). change (u_zone g') with (u_zone g).
        rewrite UD, UL. pose proof P as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
        rewrite ELS in Q9, Q11.
        destruct (complete_item (bmem_of segs (ms_mem ms)) (u_zone g) (u_root g) ls l l' Q9 Q11 CT
                    (completed_ok_wf (bmem_of segs (ms_mem ms)) (u_zone g) (ls ++ [l]) ltac:(rewrite <- ELS; exact M6))
                    ltac:(exists o0; rewrite <- SLOT, <- ELS; split; [exact TREE| exact TLC])) as (_ & CLA & CLV & _).
        exact (conj Q1 (conj Q2 (conj Q3 (conj Q4 (conj Q5 (conj Q6 (conj Q7 (conj Q8 (conj CLV (conj Q10 (conj CLA Q12))))))))))).
      *   exact O.
      *
        apply GPot.GPot.wins_ok_pot_set.
        unfold wins_ok in *. rewrite map_app. apply Forall_app. split.
        -- apply Forall_forall. intros w Hw NS. destruct (proj1 (Forall_forall _ _) Wk w Hw NS) as [D1|[NB SO]]; [left; exact D1| right].
           split; [exact NB|]. unfold sub_ok in SO |- *. cbv zeta in SO |- *.
           change (u_cstk g') with (u_cstk g). change (u_vstk g') with (u_vstk g). change (u_zone g') with (u_zone g).
           destruct SO as [A|[A|[(KK & _)|A]]]; [left; exact A| right; left; exact A| exfalso; exact (N4 w Hw KK)| right; right; right; exact A].
        -- constructor; [|constructor]. intros _. right. rewrite slot_win_den, BASE. split; [cbn [w_kind]; unfold K_BLOCK, K_SLOT; lia|].
           unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. right; right; left. split; [reflexivity|].
           exists l'. rewrite UL. split; [unfold last_opt; rewrite rev_app_distr; reflexivity|].
           cbn [CM_CONS Z.eqb Pos.eqb]. pose proof GE' as (_ & G2' & _ & G4' & _). lia.
      *
        unfold mem_ok. cbv zeta. rewrite UL.
        change (u_cstk g') with (u_cstk g). change (u_vstk g') with (u_vstk g). change (u_zone g') with (u_zone g). change (u_root g') with (u_root g).
        rewrite removelast_snoc. rewrite ELS in M1, M3, M5, M6. rewrite removelast_snoc in M1, M3.
        split; [exact M1|]. split; [intros _; exact (M2 NE)|]. split; [exact M3|]. split; [exact M4|]. split.
        -- exact (conts_at_tl_last _ (u_root g) ls l l' S7 S3 S2 M5).
        -- pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & Q9 & _ & Q11 & _). rewrite ELS in Q9, Q11.
           apply (completed_ok_item _ (u_zone g) ls l l' o0 Q9 Q11 CT M6).
           ++ rewrite <- SLOT. exact TREE.
           ++ rewrite <- SLOT, <- ELS. exact TLC.
           ++ rewrite <- ELS. exact BOD.
      *   intros X. discriminate.
      *
        destruct AX as ((X & A) & _). split; [split; [exists (X + Cost.tree_cost o0); unfold acct_ex in *; rewrite UL; change (u_zone g') with (u_zone g);
        rewrite ELS in A, DEP0;
        apply (Acct.acct_ret _ (u_zone g) ls l l' X o0 CT Vl A); [rewrite <- SLOT; exact TREE| exact (Acct.tree_cost_wf_nonneg _ _ _ TW0)| exact DEP0]|]|].
        {
          intros _. destruct PT0 as (S0 & KP0 & PA0). exists (S0 + Pot.Pot.pk10_tree o0). rewrite UL. change (u_zone g') with (u_zone g). rewrite ELS in KP0, PA0. split.
          - apply (Pot.Pot.kids_pk_ret _ (u_zone g) ls l l' S0 o0 CT Vl KP0). rewrite <- SLOT. exact TREE.
          - apply (GPot.GPot.pot_at_set E' ws (ws ++ [slot_win n]) sc _ _ SCOK).
            + intros x Hx. apply in_app_or in Hx as [Hx|[<-|[]]]; [left; exact Hx| right]. rewrite slot_win_den. cbn [w_kind]. unfold K_SLOT, K_STACK. lia.
            + pose proof (GPot.GPot.lit_value E' ws sc GPot.GPot.D_RETw _ SCOK PA0 DRET) as LV0. destruct sc as [lo|]; [| exact I].
              rewrite LV0, (Pot.Pot.pot_val_ret ls l l' S0 _ CT). reflexivity. }

        apply GPot.GPot.seal_ok_pot_set.
        change (u_zone g') with (u_zone g). rewrite map_app. apply SealX.seal_ok_app_other; [exact SE|].
        intros w [<-|[]]. rewrite slot_win_den. cbn [w_kind]. unfold Seal.K_TWIN, K_SLOT. lia.
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 1 _ (map (wden E') (GPot.GPot.pot_lit sc GPot.GPot.D_RETw (ws ++ [slot_win n]))) _ a (mk_args_sound E' 1%uint63 aw _ _ LEN'))) in FPa as (RA & NI & NW).
    assert (NW' : ~ in_ws (map (wden E') (ws ++ [slot_win n])) a) by (intros X; apply NW; apply GPot.GPot.in_ws_pot_set; exact X). clear NW. rename NW' into NW.
    rewrite map_app in NW. split.
    + left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS).
      apply (proj2 (heap_fp_iff IMGX _ 2 _ (map (wden E') ws) _ a DEC)). split; [exact RA|]. split; [exact NI|].
      intros X. apply NW. unfold in_ws in *. rewrite map_app. apply in_ivs_app. left. exact X.
    + intros k r [H|[]] IR. injection H as <- <-. apply NW. unfold in_ws. rewrite map_app. apply in_ivs_app. right.
      cbn [map]. rewrite slot_win_den. unfold in_ivs. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
      unfold inR in IR. rewrite LOZ, HIZ in IR. lia.
  -
    constructor; [| constructor; [| constructor; [| constructor]]].
    + cbn [fact_holds den]. rewrite <- EVn. apply bv_eq. exact (den_VP0 E' n wzero (weqb_refl _)).
    + cbn [fact_holds]. rewrite BASE. unfold SLOT_HI. rewrite !wlit_ok. change (to_Z 24%uint63) with 24. change (to_Z 4611686018427387904%uint63) with 4611686018427387904.
      destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch) HA (proj1 O _ OWN)) as (B1 & B2 & B3 & _).
      pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold Mem.two62Z in CEIL.
      pose proof (INB (lv_slot l') ltac:(lia)) as IV. unfold in_iv in IV.
      destruct (BYTE (lv_slot l) ltac:(lia)) as ((R0 & _) & _). lia.
    + cbn [fact_holds]. rewrite BASE. change (2 ^ to_Z 3%uint63) with 8.
      pose proof S5 as (V1 & V2 & V3 & V4 & V5). unfold lv_slot, OBJ_SIZE.
      replace (lv_P l' + 24 * lv_k l') with (lv_P l' + (3 * lv_k l') * 8) by lia. rewrite Z_mod_plus_full. exact V5.
Qed.

Theorem g3r_sound : contract_sound segs OPS MP PB g3r_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [g3r_contract c_apply] in HAP.
  destruct (g3r_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  - exfalso. unfold g3r_apply in AP.
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
  - injection HAP as <-. destruct (g3r_apply_sound E st ms model st' HS AP) as (E' & HX & HS').
    exact (Hk st' (or_introl eq_refl) E' ms model HX HMP HS').
  - exfalso. unfold g3r_apply in AP.
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End WithPc.
End G3.
