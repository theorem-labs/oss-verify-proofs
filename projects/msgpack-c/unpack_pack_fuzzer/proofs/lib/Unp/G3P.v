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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Pot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Ops GLib GUnp G3 U32 GWin.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import LiaFast.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 U32.
Open Scope Z_scope.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module G3P.

Ltac inlist := cbn [In]; repeat first [left; reflexivity | right].

Definition is_zero_decr (fs : list fact) (rc restD : sv) : bool :=
  (sv_eqb (sv_alu ALU_ADD rc (VL wone)) restD
   || msame restD (VAlu ALU_ADD rc (VL wone))
   || same32 rc (VAlu ALU_ADD restD (VL wones)))
  && match decide_eq0 fs rc with Some true => true | _ => false end.

Definition pop_type_ok (fs : list fact) (tD : sv) : bool :=
  match decide_eq fs tD (VL wzero) with Some true => true | _ =>
  match decide_eq fs tD (VL (wlit 2%uint63)) with Some true => true | _ => false end end.

Definition lit_hi (r : region) : option int :=
  match rg_hi r with VL h => if wt h then None else Some (wl h) | _ => None end.

Definition top_win (k : int) (len : int) (kd : int) : sv * sv * sv := (VP k wzero, VL (wlit len), VL (wlit kd)).

Definition region8 (cells : slot) : region :=
  Region 0%uint63 (VL (wlit 8%uint63)) true BGNone (IMap.add 0%uint63 (Gran false cells) IMap.empty).

Definition wm8 : w64 := wsub wzero (wlit 8%uint63).

Section WithPc2.
Variable POP_PC : int.

Definition g3p_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 2%uint63 then
      match ca with
      | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
          match slot, ce, ve, root with
          | VP kS os, VP kCT oce, VP kVT ove, VP kR oR =>
              let n := s_next st in let fs := s_facts st in
              if weqb os wzero && weqb oce (wlit 8%uint63) && weqb ove (wlit 8%uint63)
                 && negb (PrimInt63.eqb kS 0%uint63) && negb (PrimInt63.eqb kCT 0%uint63) && negb (PrimInt63.eqb kVT 0%uint63)
                 && negb (PrimInt63.eqb kCT kVT)
                 && negb (PrimInt63.eqb kR 0%uint63) && negb (PrimInt63.eqb kR kCT) && negb (PrimInt63.eqb kR kVT)
                 && no_slot_windows ws && st_vars_below n st && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n bit62i
                 && Z.ltb (Z.of_nat (length ws)) 4096 && pop_type_ok fs tD
                 && match decide_ltu fs cb (VP kCT oce) with Some true => true | _ => false end
              then
                match IMap.find kCT (s_regs st), IMap.find kVT (s_regs st), IMap.find kR (s_regs st) with
                | Some rc, Some rv, Some rR =>
                    match lit_hi rc, lit_hi rv, cell_at rc 4 4%uint63 with
                    | Some hc, Some hv, Some rcl =>
                        if PrimInt63.eqb (rg_lo rc) 0%uint63 && PrimInt63.eqb (rg_lo rv) 0%uint63 && rg_w rc && rg_w rv
                           && PrimInt63.leb 8%uint63 hc && PrimInt63.leb 8%uint63 hv
                           && existsb (win3_eqb (top_win kCT hc 2%uint63)) ws && existsb (win3_eqb (top_win kVT hv 3%uint63)) ws
                           && is_zero_decr fs rcl restD
                        then
                          let ws0 := List.filter (fun w => negb (win3_eqb w (top_win kCT hc 2%uint63) || win3_eqb w (top_win kVT hv 3%uint63))) ws in

                          let nV := n in
                          let wsA := ws0 ++ [top_win nV 8%uint63 3%uint63] in
                          let caA := [root; cb; cb; ccap; vb; VP nV (wlit 8%uint63); vcap; zptr; zfree; c0; VP kS wzero; tD; restD; rootT; n1; P1; zh] in
                          let rA := region8 [Cell 0%uint63 8%uint63 root] in
                          let stA := surg st [kCT; kVT] [(nV, rA)] (mk_args 2%uint63 aw wsA caA)
                                          ([FEq cb (VP kCT wzero); FEq (VP nV wzero) (VP kVT wm8); FEq (VP nV wzero) vb] ++ GW.top_facts fs vb nV)
                                          (PrimInt63.add n 1%uint63) in

                          let nC := PrimInt63.add n 1%uint63 in let nS := PrimInt63.add n 2%uint63 in
                          let nT := PrimInt63.add n 3%uint63 in let nR := PrimInt63.add n 4%uint63 in
                          let wsB := ws0 ++ [top_win nC 8%uint63 2%uint63; top_win nV 8%uint63 3%uint63] in
                          let caB := [root; cb; VP nC (wlit 8%uint63); ccap; vb; VP nV (wlit 8%uint63); vcap; zptr; zfree; c0;
                                      VP nS wzero; VP nT wzero; VP nR wzero; rootT; n1; P1; zh] in
                          let rC := region8 [Cell 0%uint63 4%uint63 (VP nT wzero); Cell 4%uint63 4%uint63 (VP nR wzero)] in
                          let rV := region8 [Cell 0%uint63 8%uint63 (VP nS wzero)] in
                          let stB := surg st [kCT; kVT] [(nV, rV); (nC, rC)] (mk_args 2%uint63 aw wsB caB)
                                          ([FNe cb (VP kCT wzero); FULt cb (VP nC (wlit 8%uint63));
                                            FEq (VP nV wzero) (VP kVT wm8); FEq (VP nC wzero) (VP kCT wm8);
                                            FRange nT wzero (wlit 2%uint63); FRange nR wone (wlit 1000%uint63);
                                            FRange nS wone (wsub wzero (wlit 25%uint63)); FAlign nS 3%uint63]
                                           ++ GW.top_facts fs vb nV ++ GW.top_facts fs cb nC)
                                          (PrimInt63.add n 5%uint63) in

                          let fA (v : sv) := if sv_eqb v (VP kCT wzero) then cb else if sv_eqb v (VP kVT wzero) then VP nV (wlit 8%uint63) else v in
                          let fB (v : sv) := if sv_eqb v (VP kCT wzero) then VP nC (wlit 8%uint63) else if sv_eqb v (VP kVT wzero) then VP nV (wlit 8%uint63) else v in
                          Some [setregs stA (IMap.add kR (GW.subst_cells fA rR) (s_regs stA));
                                setregs stB (IMap.add kR (GW.subst_cells fB rR) (s_regs stB))]
                        else None
                    | _, _, _ => None
                    end
                | _, _, _ => None
                end
              else None
          | _, _, _, _ => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Definition g3p_contract : contract := Contract POP_PC g3p_apply.

Section Sound2.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma to_Z_add_small : forall n i, to_Z n < to_Z bit62i -> to_Z i <= 8 -> to_Z (PrimInt63.add n i) = to_Z n + to_Z i.
Proof.
  intros n i Hn Hi. rewrite Uint63.add_spec. apply Z.mod_small. pose proof (int_range n). pose proof (int_range i).
  rewrite to_Z_bit62i in Hn. rewrite wB_two63. unfold two63. lia.
Qed.

Lemma ev_upd : forall E k w k', ev (env_upd E k w) k' = if PrimInt63.eqb k' k then w else ev E k'.
Proof. reflexivity. Qed.
Lemma ev_upd_other : forall E k w k', to_Z k' <> to_Z k -> ev (env_upd E k w) k' = ev E k'.
Proof.
  intros E k w k' NE. rewrite ev_upd. destruct (PrimInt63.eqb k' k) eqn:Q; [|reflexivity].
  apply Uint63.eqb_correct in Q. subst. contradiction.
Qed.

Lemma is_zero_decr_sound : forall E fs rc restD, facts_hold E fs ->
  is_zero_decr fs rc restD = true -> 1 <= bv_unsigned (den E restD) <= LIMIT -> bv_unsigned (den E restD) = 1.
Proof.
  intros E fs rc restD FH H RL. unfold is_zero_decr in H. apply andb_prop in H as [H1 H2].
  destruct (decide_eq0 fs rc) as [[|]|] eqn:D; try discriminate.
  pose proof (decide_eq0_sound E fs FH rc true D) as Z0. apply (proj1 (eqb_iff _ _ true)) in Z0.
  apply orb_prop in H1 as [H1|H3].
  2:{ pose proof (same32_sound E _ _ H3) as M. rewrite Z0, Z_to_bv_unsigned in M. change (bv_wrap 64 0 mod 2 ^ 32) with 0 in M.
      change (den E (VAlu ALU_ADD restD (VL wones))) with (alu64 ALU_ADD (den E restD) (den E (VL wones))) in M. cbn [alu64 alu den] in M.
      rewrite bv_add_unsigned, wbv_unsigned in M. change (w2Z wones) with (two64 - 1) in M. unfold bv_wrap in M. rewrite bv_modulus_64 in M.
      replace (bv_unsigned (den E restD) + (two64 - 1)) with ((bv_unsigned (den E restD) - 1) + 1 * two64) in M by (clear; lia).
      rewrite Z_mod_plus_full in M. rewrite (Z.mod_small _ two64) in M by (unfold LIMIT, two64 in *; lia).
      rewrite Z.mod_small in M by (unfold LIMIT in *; lia). lia. }
  assert (A : den E restD = alu64 ALU_ADD (den E rc) (den E (VL wone))).
  { apply orb_prop in H1 as [H1|H1].
    - apply sv_eqb_eq in H1. pose proof (den_sv_alu E ALU_ADD rc (VL wone)) as A. rewrite H1 in A. exact A.
    - exact (msame_sound E _ _ H1). }
  rewrite A. cbn [alu64 alu den]. rewrite bv_add_unsigned, wbv_unsigned, wone_ok, Z0, Z_to_bv_unsigned.
  unfold bv_wrap. rewrite bv_modulus_64. reflexivity.
Qed.

Lemma lit_hi_sound : forall E r h, lit_hi r = Some h -> hiZ E r = to_Z h.
Proof.
  intros E r h H. unfold lit_hi in H. unfold hiZ. destruct (rg_hi r); try discriminate. destruct (wt w) eqn:T; [discriminate|].
  injection H as <-. cbn [den]. rewrite wbv_unsigned. unfold w2Z. rewrite T. lia.
Qed.

Lemma top_win_den : forall E k len kd, wden E (top_win k len kd) = Win (bv_unsigned (ev E k)) (to_Z len) (to_Z kd).
Proof.
  intros E k len kd. unfold top_win, wden. rewrite (den_VP0 E k wzero (weqb_refl _)). cbn [den]. rewrite !wbv_unsigned, !wlit_ok. reflexivity.
Qed.

Lemma add_m8_8 : forall x : word, bv_add (bv_add x (wbv wm8)) (wbv (wlit 8%uint63)) = bv_add x (wbv wzero).
Proof.
  intros x. apply bv_eq. rewrite !bv_add_unsigned, !wbv_unsigned. unfold wm8. rewrite wsub_ok, wzero_ok, wlit_ok. change (to_Z 8%uint63) with 8.
  unfold bv_wrap. rewrite bv_modulus_64. unfold two64. change ((0 - 8) mod 18446744073709551616) with 18446744073709551608.
  rewrite Z.add_0_r, Zplus_mod_idemp_l. replace (bv_unsigned x + 18446744073709551608 + 8) with (bv_unsigned x + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma g3p_sound_main : forall E st ms model stA stB,
  st_ok segs OPS E st ms model -> g3p_apply st = Some [stA; stB] ->
  exists st' E', (st' = stA \/ st' = stB) /\ env_ext (s_next st) E E' /\ st_ok segs OPS E' st' ms model.
Proof.
  intros E st ms model stA stB HS0 AP.
  unfold g3p_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 2) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct slot as [|kS os| | | | | | | | |]; try discriminate.
  destruct ce as [|kCT oce| | | | | | | | |]; try discriminate.
  destruct ve as [|kVT ove| | | | | | | | |]; try discriminate.
  destruct root as [|kR oR| | | | | | | | |]; try discriminate.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  destruct (IMap.find kCT (s_regs st)) as [rc|] eqn:FC; [|discriminate].
  destruct (IMap.find kVT (s_regs st)) as [rv|] eqn:FV; [|discriminate].
  destruct (IMap.find kR (s_regs st)) as [rR|] eqn:FR; [|discriminate].
  destruct (lit_hi rc) as [hc|] eqn:HC; [|discriminate]. destruct (lit_hi rv) as [hv|] eqn:HV; [|discriminate].
  destruct (cell_at rc 4 4%uint63) as [rcl|] eqn:CRC; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND2; [|discriminate] end.
  injection AP as EA EB.
  set (root := VP kR oR) in *.
  apply andb_prop in COND as [COND DLT]. apply andb_prop in COND as [COND PT].
  apply andb_prop in COND as [COND WLEN]. apply Z.ltb_lt in WLEN.
  apply andb_prop in COND as [COND N62]. apply andb_prop in COND as [COND NPOS]. apply andb_prop in COND as [COND VB].
  apply andb_prop in COND as [COND NSW]. apply andb_prop in COND as [COND KRV]. apply andb_prop in COND as [COND KRC]. apply andb_prop in COND as [COND KR0].
  apply andb_prop in COND as [COND KCV].
  apply negb_true_iff in KRV. apply negb_true_iff in KRC. apply negb_true_iff in KR0.
  apply andb_prop in COND as [COND KVT0]. apply andb_prop in COND as [COND KCT0]. apply andb_prop in COND as [COND KS0].
  apply andb_prop in COND as [COND OVE]. apply andb_prop in COND as [OS OCE].
  apply (proj1 (weqb_ok _ _)) in OS. apply (proj1 (weqb_ok _ _)) in OCE. apply (proj1 (weqb_ok _ _)) in OVE. subst os oce ove.
  apply negb_true_iff in KS0. apply negb_true_iff in KCT0. apply negb_true_iff in KVT0. apply negb_true_iff in KCV.
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in N62.
  apply andb_prop in COND2 as [COND2 ZD]. apply andb_prop in COND2 as [COND2 EXV]. apply andb_prop in COND2 as [COND2 EXC].
  apply andb_prop in COND2 as [COND2 HV8]. apply andb_prop in COND2 as [COND2 HC8].
  apply Uint63.leb_spec in HV8. apply Uint63.leb_spec in HC8. change (to_Z 8%uint63) with 8 in HV8, HC8.
  apply andb_prop in COND2 as [COND2 WV]. apply andb_prop in COND2 as [COND2 WC]. apply andb_prop in COND2 as [LOC LOV].
  apply Uint63.eqb_correct in LOC. apply Uint63.eqb_correct in LOV.
  set (n := s_next st) in *.

  destruct (the_op_full st 2%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  assert (INCA : forall v, In v [root; cb; VP kCT (wlit 8); ccap; vb; VP kVT (wlit 8); vcap; zptr; zfree; c0; VP kS wzero; tD; restD; rootT; n1; P1; zh] ->
                           In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (INAW : In aw (op_args o)) by (rewrite ARGS; right; left; reflexivity).
  pose proof (ops_vars_below n st o VB (op_in_In st o OPS1)) as VBo.
  assert (KCTn : PrimInt63.ltb kCT n = true) by exact (VBo (VP kCT (wlit 8)) (INCA (VP kCT (wlit 8)) ltac:(do 2 right; left; reflexivity))).
  assert (KVTn : PrimInt63.ltb kVT n = true) by exact (VBo (VP kVT (wlit 8)) (INCA (VP kVT (wlit 8)) ltac:(do 5 right; left; reflexivity))).
  apply Uint63.ltb_spec in KCTn. apply Uint63.ltb_spec in KVTn.
  pose proof (to_Z_add_small n 1%uint63 N62 ltac:(change (to_Z 1%uint63) with 1; lia)) as AD1.
  pose proof (to_Z_add_small n 2%uint63 N62 ltac:(change (to_Z 2%uint63) with 2; lia)) as AD2.
  pose proof (to_Z_add_small n 3%uint63 N62 ltac:(change (to_Z 3%uint63) with 3; lia)) as AD3.
  pose proof (to_Z_add_small n 4%uint63 N62 ltac:(change (to_Z 4%uint63) with 4; lia)) as AD4.
  pose proof (to_Z_add_small n 5%uint63 N62 ltac:(change (to_Z 5%uint63) with 5; lia)) as AD5.
  change (to_Z 1%uint63) with 1 in AD1. change (to_Z 2%uint63) with 2 in AD2. change (to_Z 3%uint63) with 3 in AD3.
  change (to_Z 4%uint63) with 4 in AD4. change (to_Z 5%uint63) with 5 in AD5.

  pose proof HS0 as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HCW).
  pose proof (DECf E) as DEC.
  rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 2%uint63) with 2 in HCW.
  cbn [cw_holds unp_cw] in HCW. unfold cw_unp_holds in HCW. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HCW.
  cbn [map decode_uc] in HCW.
  destruct HCW as (g & L & P & O & Wk & M & CS0 & AX & SE).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap, Lzp, Lzf, Lc0, LD.
  cbn [den] in Lcb, Lce, Lve.
  pose proof (pf g P) as (VC & EC & SC & VV & EV & SV' & LV & LA & ZV).
  pose proof VC as (VC1 & VC2 & VC3 & VC4). pose proof VV as (VV1 & VV2 & VV3 & VV4).
  destruct M as (M1 & M2 & M3 & M4 & M5 & M6).
  destruct (CS0 eq_refl) as (o0 & TW0 & KA0 & HD0 & _ & TLC & BOD & DEP0 & PT0).

  assert (NE : u_levels g <> []).
  { destruct (decide_ltu (s_facts st) cb (VP kCT (wlit 8))) as [[|]|] eqn:DL; try discriminate.
    pose proof (decide_ltu_sound E (s_facts st) Pfacts _ _ _ DL) as LT. apply (proj1 (ltu_iff _ _ true)) in LT.
    cbn [den] in LT. rewrite <- Lcb, <- Lce in LT. unfold v_end in LT. rewrite EC, SC in LT.
    intros X. unfold u_D in LT. rewrite X in LT. cbn [length Z.of_nat] in LT. lia. }
  destruct (LD NE) as (Lslot & (lD & HlD & LtD & LrD) & (l1 & ls1 & E1 & LT1 & LN1 & LP1)).
  cbn [c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lslot, LtD, LrD, LT1, LN1, LP1.
  destruct (exists_last NE) as (ls & l & ELS).
  assert (HlD' : lD = l) by (rewrite ELS in HlD; unfold last_opt in HlD; rewrite rev_app_distr in HlD; cbn in HlD; congruence).
  subst lD.
  assert (INl : In l (u_levels g)) by (rewrite ELS; apply in_app_iff; right; left; reflexivity).
  assert (Vl : level_valid l) by exact (proj1 (Forall_forall _ _) LV l INl).
  assert (SLOT : u_cur_slot g = lv_slot l) by (unfold u_cur_slot; rewrite ELS; apply cur_slot_snoc).
  assert (TREE : tree_at (bmem_of segs (ms_mem ms)) (u_zone g) (lv_slot l) o0).
  { rewrite <- SLOT. split; [| exact TW0]. apply (proj2 (obj_at_split _ _ _)). split; [exact (HD0 NE)| exact KA0]. }

  pose proof Vl as (VR1 & VR2 & VR3 & _).
  pose proof (is_zero_decr_sound E (s_facts st) rcl restD Pfacts ZD ltac:(rewrite <- LrD; unfold LIMIT in *; lia)) as R1. rewrite <- LrD in R1.
  assert (CT : consume_top l = CS_Pop).
  { unfold pop_type_ok in PT. unfold consume_top.
    assert (TC : forall w, decide_eq (s_facts st) tD (VL w) = Some true -> ctype_code (lv_t l) = w2Z w).
    { intros w Hd. pose proof (decide_eq_sound E (s_facts st) Pfacts tD (VL w) true Hd) as Q.
      apply (proj1 (eqb_iff _ _ true)) in Q. rewrite LtD, Q. cbn [den]. apply wbv_unsigned. }
    destruct (decide_eq (s_facts st) tD (VL wzero)) as [[|]|] eqn:D0.
    1: { pose proof (TC wzero D0) as T0. rewrite wzero_ok in T0. destruct (lv_t l); cbn in T0; try lia. rewrite R1. reflexivity. }
    all: destruct (decide_eq (s_facts st) tD (VL (wlit 2))) as [[|]|] eqn:D2; try discriminate.
    all: pose proof (TC (wlit 2) D2) as T2; rewrite wlit_ok in T2; change (to_Z 2%uint63) with 2 in T2;
         destruct (lv_t l); cbn in T2; try lia; rewrite R1; reflexivity. }

  pose proof P as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12).
  assert (HO : OBJ_SIZE = 24) by reflexivity.

  assert (DLEN : u_D g = Z.of_nat (length ls) + 1) by (unfold u_D; rewrite ELS, length_app; cbn [length]; lia).
  assert (KCTv : bv_unsigned (ev E kCT) = v_end (u_cstk g) - 8).
  { rewrite Lce, bv_add_unsigned, wbv_unsigned, wlit_ok. change (to_Z 8%uint63) with 8.
    pose proof (ro_range _ _ _ _ _ _ (Preg kCT rc FC) KCT0) as [_ RR2].
    pose proof (bv_unsigned_in_range _ (ev E kCT)) as RK. rewrite bv_modulus_64 in RK.
    rewrite (lit_hi_sound E rc hc HC) in RR2.
    unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.mod_small; lia. }
  assert (KVTv : bv_unsigned (ev E kVT) = v_end (u_vstk g) - 8).
  { rewrite Lve, bv_add_unsigned, wbv_unsigned, wlit_ok. change (to_Z 8%uint63) with 8.
    pose proof (ro_range _ _ _ _ _ _ (Preg kVT rv FV) KVT0) as [_ RR2].
    pose proof (bv_unsigned_in_range _ (ev E kVT)) as RK. rewrite bv_modulus_64 in RK.
    rewrite (lit_hi_sound E rv hv HV) in RR2.
    unfold bv_wrap. rewrite bv_modulus_64. rewrite Z.mod_small; lia. }

  pose proof Q9 as Q9'. pose proof Q11 as Q11'. rewrite ELS in Q9', Q11'.
  pose proof M6 as M6'. rewrite ELS in M6'.
  destruct (complete_container_ok (bmem_of segs (ms_mem ms)) (u_zone g) ls l (cur_slot (u_root g) ls) Q9' Q11' Q12 CT M6'
              ltac:(exists o0; split; [exact TREE| rewrite <- SLOT, <- ELS; split; [exact TLC| exact BOD]]))
    as (oc & OT & OCNT & OPTR & OTW & OKA & OHD & OCELLS & OBOD & CWls & LAls & Vls).

  destruct AX as ((XA & AA) & _). rewrite ELS in AA, DEP0.
  destruct (container_depth_acct (bmem_of segs (ms_mem ms)) (u_zone g) ls l XA o0 oc Vl CT AA TREE DEP0 OT OCNT OPTR OTW OKA) as (DEPC & AXls).

  destruct PT0 as (S0 & KP0 & PA0). rewrite ELS in KP0, PA0.
  destruct (Pot.Pot.kids_pk_pop_k (bmem_of segs (ms_mem ms)) (u_zone g) ls l S0 o0 oc CT Vl KP0 TREE OTW OKA OT OCNT OPTR) as (S1 & KP1 & PEQ).
  pose proof (Pot.Pot.pot_val_pop ls l S0 S1 (Pot.Pot.pk10_tree o0) (Pot.Pot.pk10_tree oc) CT PEQ) as PVP.
  assert (POTgen : forall E' wsN, map (wden E') ws = map (wden E) ws -> (forall x, In x wsN -> In x ws \/ w_kind (wden E' x) <> K_STACK) ->
            pot_at (map (wden E') wsN) (Pot.Pot.pot_val ls S1 (Pot.Pot.pk10_tree oc))).
  { intros E' wsN WE HN. rewrite PVP. apply (pot_at_ws _ _ _ PA0). rewrite <- WE. exact (UOK.pot_map_old E' ws wsN HN). }

  pose proof (owned_cstk g) as OWC. pose proof (owned_vstk g) as OWV.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (cstk_block g) HA (proj1 O _ OWC)) as (BC1 & BC2 & BC3 & BC4 & _).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (vstk_block g) HA (proj1 O _ OWV)) as (BV1 & BV2 & BV3 & BV4 & _).
  cbn [cstk_block vstk_block fst snd] in BC1, BC2, BC3, BV1, BV2, BV3. unfold v_bytes in BC3, BV3.
  assert (BYC : forall a, v_begin (u_cstk g) <= a < v_end (u_cstk g) - 8 ->
            (0 <= a /\ a + 1 < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws (map (wden E) ws) a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (owned_byte_props segs IMGX AW _ LB (ms_mem ms) model 2 g (map (wden E) ws) (cstk_block g) a HA WF O Wk OWC).
    - unfold in_iv, cstk_block. cbn [fst snd]. unfold v_bytes, v_end in *. rewrite EC in *. nia.
    - exact (safe_cstk 2 g LB (map (wden E) ws) P O a Ha). }
  assert (BYV : forall a, v_begin (u_vstk g) <= a < v_end (u_vstk g) - 8 ->
            (0 <= a /\ a + 1 < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws (map (wden E) ws) a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (owned_byte_props segs IMGX AW _ LB (ms_mem ms) model 2 g (map (wden E) ws) (vstk_block g) a HA WF O Wk OWV).
    - unfold in_iv, vstk_block. cbn [fst snd]. unfold v_bytes, v_end in *. rewrite EV in *. nia.
    - exact (safe_vstk 2 g LB (map (wden E) ws) P O a Ha). }

  assert (DRgen : forall E', env_ext n E E' -> forall v, In v (op_args o) -> den E' v = den E v).
  { intros E' HX v Hv. exact (den_reval n E E' HX v (VBo v Hv)). }
  assert (INWS : forall a b c, In (a, b, c) ws -> In a (op_args o) /\ In b (op_args o) /\ In c (op_args o)).
  { intros a b c Hw. destruct (in_flat_windows ws a b c Hw) as (A1 & A2 & A3). rewrite ARGS.
    split; [| split]; right; right; right; apply in_app_iff; left; assumption. }
  assert (WDRgen : forall E', env_ext n E E' -> forall ws1, (forall w, In w ws1 -> In w ws) -> map (wden E') ws1 = map (wden E) ws1).
  { intros E' HX ws1 SUB. apply map_ext_in. intros [[a b] c] Hw. destruct (INWS a b c (SUB _ Hw)) as (A1 & A2 & A3).
    unfold wden. rewrite !(DRgen E' HX) by assumption. reflexivity. }

  set (ws0 := List.filter (fun w => negb (win3_eqb w (top_win kCT hc 2) || win3_eqb w (top_win kVT hv 3))) ws) in *.
  assert (SUB0 : forall w, In w ws0 -> In w ws /\ w <> top_win kCT hc 2%uint63 /\ w <> top_win kVT hv 3%uint63).
  { intros w Hw. apply filter_In in Hw as [Hw NS]. split; [exact Hw|].
    split; intros ->; rewrite win3_eqb_refl in NS; cbn in NS; try discriminate. rewrite orb_true_r in NS. discriminate. }
  pose proof (no_slot_windows_sound E ws NSW) as NSL.

  assert (HIC : hiZ E rc = to_Z hc) by exact (lit_hi_sound E rc hc HC).
  assert (HIV : hiZ E rv = to_Z hv) by exact (lit_hi_sound E rv hv HV).
  assert (LOC' : loZ rc = 0) by (unfold loZ, keyZ, Mem.keyZ; rewrite LOC; reflexivity).
  assert (LOV' : loZ rv = 0) by (unfold loZ, keyZ, Mem.keyZ; rewrite LOV; reflexivity).
  assert (REMOVED : forall E', env_ext n E E' -> forall a, in_ws (map (wden E') ws) a -> ~ in_ws (map (wden E') ws0) a ->
             exists k r, In k [kCT; kVT] /\ IMap.find k (s_regs st) = Some r /\ inR E' k r a).
  { intros E' HX a IN NIN. rewrite (WDRgen E' HX ws ltac:(auto)) in IN. rewrite (WDRgen E' HX ws0 ltac:(intros w Hw; exact (proj1 (SUB0 w Hw)))) in NIN.
    apply in_ws_map_iff in IN as (x & Hx & Ha).
    destruct (win3_eqb x (top_win kCT hc 2) || win3_eqb x (top_win kVT hv 3)) eqn:ISW.
    - apply orb_prop in ISW as [ISW|ISW]; apply win3_eqb_eq in ISW; subst x; rewrite top_win_den in Ha; unfold in_iv, w_iv in Ha; cbn [w_lo w_len fst snd] in Ha.
      + exists kCT, rc. split; [left; reflexivity|]. split; [exact FC|]. unfold inR. rewrite (ev_reval n E E' HX kCT ltac:(apply Uint63.ltb_spec; exact KCTn)).
        rewrite (lit_hi_sound E' rc hc HC), LOC'. lia.
      + exists kVT, rv. split; [right; left; reflexivity|]. split; [exact FV|]. unfold inR. rewrite (ev_reval n E E' HX kVT ltac:(apply Uint63.ltb_spec; exact KVTn)).
        rewrite (lit_hi_sound E' rv hv HV), LOV'. lia.
    - exfalso. apply NIN. apply in_ws_map_iff. exists x. split; [|exact Ha]. apply filter_In. split; [exact Hx|]. rewrite ISW. reflexivity. }
  assert (LEN0 : (length ws0 <= length ws)%nat) by (subst ws0; apply filter_length_le).
  assert (NZ : PrimInt63.eqb n 0%uint63 = false) by (apply (proj2 (Uint63.eqb_false_spec _ _)); intros X; rewrite X in NPOS; change (to_Z 0%uint63) with 0 in NPOS; lia).
  assert (KSall : forall k, In k [kCT; kVT] -> PrimInt63.eqb k 0%uint63 = false /\ exists r, IMap.find k (s_regs st) = Some r /\ rg_w r = true).
  { intros k [<-|[<-|[]]]; [split; [exact KCT0| exists rc; auto]| split; [exact KVT0| exists rv; auto]]. }

  assert (FPold : forall E', env_ext n E E' -> forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E) ws) a ->
            FP OPS E' (op_args o) a).
  { intros E' HX a RA NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS).
    rewrite (map_ext_in (den E') (den E) (op_args o) (DRgen E' HX)).
    apply (proj2 (heap_fp_iff IMGX _ 2 _ (map (wden E) ws) _ a DEC)). split; [lia| auto]. }

  destruct ls as [|lfst lrest].
  -
    cbn [app] in ELS.
    set (wV := bv_add (ev E kVT) (wbv wm8)).
    set (E' := env_upd E n wV).
    assert (HX : env_ext n E E') by apply env_upd_ext.
    assert (EVn : ev E' n = wV) by apply env_upd_same.
    pose proof (DRgen E' HX) as DR. pose proof (WDRgen E' HX) as WDR.
    assert (EVkVT : ev E' kVT = ev E kVT) by exact (ev_reval n E E' HX kVT ltac:(apply Uint63.ltb_spec; exact KVTn)).
    assert (EVkCT : ev E' kCT = ev E kCT) by exact (ev_reval n E E' HX kCT ltac:(apply Uint63.ltb_spec; exact KCTn)).
    clearbody E'.
    assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
    assert (D1 : u_D g = 1) by (rewrite DLEN; cbn [length Z.of_nat]; lia).
    assert (VBASE : bv_unsigned (ev E' n) = v_begin (u_vstk g)).
    { rewrite EVn. subst wV. rewrite bv_add_unsigned, wbv_unsigned, KVTv. unfold wm8. rewrite wsub_ok, wzero_ok, wlit_ok. change (to_Z 8%uint63) with 8.
      unfold v_end. rewrite EV, SV', D1. unfold bv_wrap. rewrite bv_modulus_64. unfold two64.
      replace (v_begin (u_vstk g) + 8 * (1 + 1) - 8 + (0 - 8) mod 18446744073709551616) with (v_begin (u_vstk g) + 1 * 18446744073709551616) by
        (change ((0 - 8) mod 18446744073709551616) with 18446744073709551608; lia).
      rewrite Z_mod_plus_full. apply Z.mod_small. unfold two64 in BV4. lia. }
    set (rA := region8 [Cell 0%uint63 8%uint63 root]) in *.
    assert (HIA : forall Ex, hiZ Ex rA = 8) by (intros Ex; reflexivity).
    assert (LOA : loZ rA = 0) by reflexivity.
    set (wsA := ws0 ++ [top_win n 8%uint63 3%uint63]) in *.
    set (caA := [root; cb; cb; ccap; vb; VP n (wlit 8%uint63); vcap; zptr; zfree; c0; VP kS wzero; tD; restD; rootT; n1; P1; zh]) in *.
    assert (LENA : Z.of_nat (length wsA) < two63) by (subst wsA; rewrite length_app; cbn [length]; unfold two63; lia).
    assert (VE16 : v_begin (u_vstk g) + 16 = v_end (u_vstk g)) by (unfold v_end; rewrite EV, SV', D1; lia).
    assert (BYA : forall a, v_begin (u_vstk g) <= a < v_begin (u_vstk g) + 8 ->
              (0 <= a /\ a + 1 < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws (map (wden E) ws) a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
    { intros a Ha. apply BYV. lia. }
    assert (KRn : to_Z kR < to_Z n).
    { pose proof (VBo root (INCA root ltac:(left; reflexivity))) as X. unfold root in X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
    exists stA, E'. split; [left; reflexivity|]. split; [exact HX|]. subst stA.
    match goal with |- st_ok _ _ _ (setregs ?S1 (IMap.add _ _ ?R)) _ _ => change R with (s_regs S1) end.
    apply (GW.st_ok_subst_cells segs OPS E' _ ms model kR rR); [| | exact KR0|].
    2:{ cbn [surg s_regs]. assert (NDA : List.NoDup (map fst [(n, rA)])) by (cbn [map fst]; constructor; [intros []| constructor]).
        apply (proj2 (find_add_regions _ _ kR rR (remove_keys_bst _ _ Pbst) NDA)).
        right. split; [cbn [map fst In]; intros [X|[]]; rewrite X in KRn; lia|].
        apply (proj2 (find_remove_keys _ _ kR rR Pbst)). split; [| exact FR].
        cbn [In]. intros [X|[X|[]]]; [rewrite X, Uint63.eqb_refl in KRC; discriminate| rewrite X, Uint63.eqb_refl in KRV; discriminate]. }
    2:{ intros v. destruct (sv_eqb v (VP kCT wzero)) eqn:QF1.
        - apply sv_eqb_eq in QF1. subst v. apply bv_eq. rewrite (DR cb (INCA cb ltac:(right; left; reflexivity))).
          rewrite (den_VP0 E' kCT wzero (weqb_refl _)), EVkCT, KCTv, <- Lcb. unfold v_end. rewrite EC, SC, D1. lia.
        - destruct (sv_eqb v (VP kVT wzero)) eqn:QF2; [|reflexivity]. apply sv_eqb_eq in QF2. subst v. cbn [den]. rewrite EVn, EVkVT. subst wV.
          apply add_m8_8. }
    apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [kCT; kVT] [(n, rA)] (mk_args 2%uint63 aw wsA caA) _ (PrimInt63.add n 1)).
    + exact KSall.
    + constructor; [intros []| constructor].
    + intros k r [H|[]]. injection H as <- <-. exact NZ.
    +
      intros k r [H|[]]. injection H as <- <-.
      apply (region_ok_fresh segs (s_priv st) E' (ms_mem ms) n rA NZ).
      * cbn [rA region8 rg_cells]. apply IMap.bst_add. exact I.
      * reflexivity.
      * rewrite VBASE, LOA. lia.
      * rewrite VBASE, HIA. destruct (BYA (v_begin (u_vstk g) + 7) ltac:(lia)) as (R & _). lia.
      * intros a Ha. rewrite VBASE, LOA, HIA in Ha. destruct (BYA a ltac:(lia)) as (_ & _ & _ & MT & NSG). auto.
      * intros gk gr F. cbn [rA region8 rg_cells] in F.
        destruct (Uint63.eqb gk 0) eqn:GK.
        -- apply Uint63.eqb_correct in GK. subst gk. rewrite IMap.find_add_same in F by exact I. injection F as <-. cbn [g_cells].
           change (keyZ 0%uint63) with 0. rewrite Z.mul_0_r, Z.add_0_r. split.
           ++ split; [cbn; tauto|]. constructor; [|constructor].
              apply (cell_ok_of_u64 segs E' (ms_mem ms) (bv_unsigned (ev E' n)) 0%uint63 root (u_root g)); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
              ** change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, VBASE. apply M2. exact NE.
              ** rewrite (DR root (INCA root ltac:(left; reflexivity))). symmetry. exact Lroot.
           ++ intros c i [<-|[]] Hi. cbn [c_w c_idx] in Hi |- *. change (to_Z 8%uint63) with 8 in Hi. change (to_Z 0%uint63) with 0. rewrite LOA, HIA. lia.
        -- apply Uint63.eqb_false_correct in GK. rewrite IMap.find_add_other in F by (try exact I; congruence). rewrite IMap.find_empty in F. discriminate.
    +
      intros k r a [H|[]] IR. injection H as <- <-. unfold inR in IR. rewrite VBASE, LOA, HIA in IR.
      destruct (BYA a ltac:(lia)) as (RA & NI & NW & _). left. exact (FPold E' HX a ltac:(lia) NI NW).
    + intros k1 r1 k2 r2 a [H1|[]] [H2|[]] NE12. injection H1 as <- <-. injection H2 as <- <-. contradiction.
    +
      rewrite (ho_holds _ _ _ _ _ HOPS).
      exists 2, (den E' aw), (map (wden E') wsA), (map (den E') caA), LB.
      split; [apply mk_args_sound; exact LENA|].

      split; [rewrite (DR aw INAW); apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); rewrite <- (WDR ws ltac:(auto));
              assert (WkE' : wins_ok 2 g (map (wden E') ws)) by (rewrite (WDR ws ltac:(auto)); exact Wk);
              apply (UOK.unp_wins_keep_map E' 2 g LB ws wsA P O WkE');
              [intros x Hx; subst wsA; apply in_app_or in Hx as [Hx|Hx]; [left; exact (proj1 (SUB0 x Hx))| right; left];
               destruct Hx as [<-|[]]; apply UOK.kind_sub; vm_compute; reflexivity
              |intros x Hx; destruct (win3_eqb x (top_win kCT hc 2)) eqn:QK1;
               [right; left; apply win3_eqb_eq in QK1; subst x; apply UOK.kind_sub; vm_compute; reflexivity|];
               destruct (win3_eqb x (top_win kVT hv 3)) eqn:QK2;
               [right; left; apply win3_eqb_eq in QK2; subst x; apply UOK.kind_sub; vm_compute; reflexivity|];
               left; subst wsA; apply in_or_app; left; subst ws0; apply filter_In; split; [exact Hx|]; cbv beta; rewrite QK1, QK2; reflexivity]|]. split.
      *
        unfold windows_wf in *. subst wsA. rewrite map_app. apply Forall_app. split.
        -- rewrite (WDR ws0 ltac:(intros w Hw; exact (proj1 (SUB0 w Hw)))). apply Forall_forall. intros w Hw.
           apply in_map_iff in Hw as (x & <- & Hx). exact (proj1 (Forall_forall _ _) WF (wden E x) (in_map _ _ _ (proj1 (SUB0 x Hx)))).
        -- constructor; [|constructor]. rewrite top_win_den, VBASE. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. change (to_Z 8%uint63) with 8. change (to_Z 3%uint63) with 3.
           split; [lia|]. split; [lia|]. split; [unfold two64 in *; nia|].
           right; right. split; [unfold K_SUB; lia|]. exists (vstk_block g). split; [exact (proj1 O _ OWV)|].
           intros a Ha. unfold in_iv, vstk_block, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. unfold v_bytes. rewrite EV. clear - Ha VV2 SV' D1. nia.
      *
        cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. subst caA. cbn [map decode_uc].
        set (gA := mkUnp (u_ctx g) (u_vis g) (u_data g) (u_len g) [] (vec_pop (u_cstk g)) (vec_pop (u_vstk g)) (u_zone g)).
        destruct (vec_pop_valid (u_cstk g) VC ltac:(rewrite SC, D1; lia)) as [VCP CEP].
        destruct (vec_pop_valid (u_vstk g) VV ltac:(rewrite SV', D1; lia)) as [VVP VEP].
        exists gA. split; [| split; [| split; [| split; [| split; [| split]]]]].
        --
           unfold link. cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1].
           change (u_root gA) with (u_root g). change (u_cstk gA) with (vec_pop (u_cstk g)). change (u_vstk gA) with (vec_pop (u_vstk g)).
           change (u_zone gA) with (u_zone g). change (u_levels gA) with (@nil level).
           rewrite (DR root), (DR cb), (DR ccap), (DR vb), (DR vcap), (DR zptr), (DR zfree), (DR c0) by (apply INCA; inlist).
           rewrite CEP, VEP, EC, EV.
           change (v_begin (vec_pop (u_cstk g))) with (v_begin (u_cstk g)). change (v_begin (vec_pop (u_vstk g))) with (v_begin (u_vstk g)).
           change (v_capend (vec_pop (u_cstk g))) with (v_capend (u_cstk g)). change (v_capend (vec_pop (u_vstk g))) with (v_capend (u_vstk g)).
           split; [exact Lroot|]. split; [exact Lcb|]. split; [rewrite <- Lcb; unfold v_end; rewrite EC, SC, D1; lia|]. split; [exact Lccap|].
           split; [exact Lvb|]. split; [| split; [exact Lvcap| split; [exact Lzp| split; [exact Lzf| split; [exact Lc0| intros X; exfalso; exact (X eq_refl)]]]]].
           cbn [den]. rewrite bv_add_unsigned, wbv_unsigned, wlit_ok, VBASE. change (to_Z 8%uint63) with 8.
           unfold bv_wrap. rewrite bv_modulus_64, Z.mod_small by (unfold two64 in *; lia). lia.
        --
           unfold pure_ok. change (u_cstk gA) with (vec_pop (u_cstk g)). change (u_vstk gA) with (vec_pop (u_vstk g)).
           change (u_zone gA) with (u_zone g). change (u_levels gA) with (@nil level). change (u_D gA) with 0.
           change (v_elt (vec_pop (u_cstk g))) with (v_elt (u_cstk g)). change (v_elt (vec_pop (u_vstk g))) with (v_elt (u_vstk g)).
           change (v_size (vec_pop (u_cstk g))) with (v_size (u_cstk g) - 1). change (v_size (vec_pop (u_vstk g))) with (v_size (u_vstk g) - 1).
           change (v_cap (vec_pop (u_cstk g))) with (v_cap (u_cstk g)). change (v_cap (vec_pop (u_vstk g))) with (v_cap (u_vstk g)).
           rewrite SC, SV', D1.
           split; [exact VCP|]. split; [exact EC|]. split; [lia|]. split; [exact Q4|]. split; [exact VVP|]. split; [exact EV|]. split; [lia|]. split; [exact Q8|].
           split; [constructor|]. split; [unfold LIMIT; lia|]. split; [exact LAls| exact Q12].
        --   exact O.
        --
           unfold wins_ok in *. subst wsA. rewrite map_app. apply Forall_app. split.
           ++ rewrite (WDR ws0 ltac:(intros w Hw; exact (proj1 (SUB0 w Hw)))). apply Forall_forall. intros w Hw NS.
              apply in_map_iff in Hw as (x & <- & Hx). destruct (SUB0 x Hx) as (Hx0 & _ & _).
              destruct (proj1 (Forall_forall _ _) Wk (wden E x) (in_map _ _ _ Hx0) NS) as [DJ|[NB SO]]; [left; exact DJ| right].
              split; [exact NB|]. unfold sub_ok in SO |- *. cbv zeta in SO |- *.
              change (u_cstk gA) with (vec_pop (u_cstk g)). change (u_vstk gA) with (vec_pop (u_vstk g)). change (u_zone gA) with (u_zone g). change (u_levels gA) with (@nil level).
              rewrite CEP, VEP. change (v_begin (vec_pop (u_cstk g))) with (v_begin (u_cstk g)). change (v_begin (vec_pop (u_vstk g))) with (v_begin (u_vstk g)).
              change (v_capend (vec_pop (u_cstk g))) with (v_capend (u_cstk g)). change (v_capend (vec_pop (u_vstk g))) with (v_capend (u_vstk g)).
              destruct SO as [(KK & A1 & A2 & A3)|[(KK & A1 & A2 & A3)|[(KK & _)|A]]];
                [left; rewrite EC; repeat split; auto; lia| right; left; rewrite EV; repeat split; auto; lia| exfalso; exact (NSL _ (in_map _ _ _ Hx0) KK)| right; right; right; exact A].
           ++ constructor; [|constructor]. intros _. right. rewrite top_win_den, VBASE. split; [cbn [w_kind]; unfold K_BLOCK; change (to_Z 3%uint63) with 3; lia|].
              unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. change (to_Z 3%uint63) with 3. change (to_Z 8%uint63) with 8. right; left. split; [reflexivity|].
              change (u_vstk gA) with (vec_pop (u_vstk g)). rewrite VEP, EV.
              change (v_begin (vec_pop (u_vstk g))) with (v_begin (u_vstk g)). change (v_capend (vec_pop (u_vstk g))) with (v_capend (u_vstk g)).
              unfold v_capend, v_end in *. rewrite EV in *. pose proof VV2. nia.
        --
           unfold mem_ok. cbv zeta. change (u_levels gA) with (@nil level). change (u_zone gA) with (u_zone g). change (u_root gA) with (u_root g).
           cbn [removelast cstk_at vstk_at containers tl conts_at]. split; [exact I|]. split; [intros X; exfalso; exact (X eq_refl)|]. split; [exact I|].
           split; [exact M4|]. split; [exact I|]. intros lx [].
        --
           intros _. cbv zeta. change (u_levels gA) with (@nil level). change (u_zone gA) with (u_zone g).
           change (u_cur_slot gA) with (cur_slot (u_root g) []). rewrite cur_slot_nil.
           cbn [c_rootT c_n1 c_P1]. rewrite (DR rootT), (DR n1), (DR P1) by (apply INCA; inlist).
           exists oc. split; [exact OTW|]. split; [exact OKA|]. split; [intros X; exfalso; exact (X eq_refl)|]. split.
           ++ intros _. rewrite ELS in E1. injection E1 as <- <-. rewrite (obj_cnt_of_type oc ltac:(rewrite OT; destruct (lv_t l); cbn; auto)), OT, OCNT, OPTR. auto.
           ++ split; [| split; [exact OBOD| split; [cbn [length]; lia|]]]; [rewrite cur_slot_nil in OCELLS; exact OCELLS|].
              exists S1. split; [exact KP1|]. apply (POTgen E' wsA (WDR ws ltac:(auto))).
              intros x Hx. subst wsA. apply in_app_or in Hx as [Hx|[<-|[]]]; [left; exact (proj1 (SUB0 x Hx))| right; apply kind_ne; vm_compute; reflexivity].
        --   split; [split; [exists 0; change (u_levels gA) with (@nil level); apply Acct.acct_nil; lia| intros X; discriminate X]|].

           change (u_zone gA) with (u_zone g). subst wsA. rewrite map_app. apply SealX.seal_ok_app_other.
           ++ rewrite (WDR ws0 ltac:(intros w Hw; exact (proj1 (SUB0 w Hw)))). apply (SealX.seal_ok_map _ _ _ _ _ SE). intros x Hx. left. exact (proj1 (SUB0 x Hx)).
           ++ intros w [<-|[]]. apply kind_ne. vm_compute. reflexivity.
    +
      intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
      apply (proj1 (heap_fp_iff IMGX _ 2 _ (map (wden E') wsA) _ a (mk_args_sound E' 2%uint63 aw _ _ LENA))) in FPa as (RA & NI & NW).
      subst wsA. rewrite map_app in NW. split.
      * destruct (in_ws_dec (map (wden E') ws) a) as [IN|NIN].
        -- right. apply (REMOVED E' HX a IN). intros X. apply NW. unfold in_ws in *. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). left. exact X.
        -- left. rewrite (WDR ws ltac:(auto)) in NIN. exact (FPold E' HX a RA NI NIN).
      * intros k r [H|[]] IR. injection H as <- <-. apply NW. unfold in_ws. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). right.
        cbn [map]. rewrite top_win_den. unfold in_ivs. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
        unfold inR in IR. rewrite LOA, HIA in IR. change (to_Z 8%uint63) with 8. lia.
    +
      constructor; [| constructor; [| constructor]].
      * cbn [fact_holds]. apply bv_eq. rewrite (DR cb (INCA cb ltac:(right; left; reflexivity))).
        rewrite (den_VP0 E' kCT wzero (weqb_refl _)), EVkCT, KCTv, <- Lcb. unfold v_end. rewrite EC, SC, D1. lia.
      * cbn [fact_holds den]. rewrite EVkVT. fold wV. rewrite <- EVn. apply bv_eq. exact (den_VP0 E' n wzero (weqb_refl _)).
      *
        cbn [fact_holds]. apply bv_eq. rewrite (den_VP0 E' n wzero (weqb_refl _)), VBASE.
        rewrite (DR vb (INCA vb ltac:(do 4 right; left; reflexivity))), <- Lvb. reflexivity.
      * pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold Mem.two62Z in CEIL.
        apply GW.top_facts_sound; [exact (so_facts _ _ _ _ _ _ HS)| |];
          rewrite (DR vb (INCA vb ltac:(do 4 right; left; reflexivity))), <- Lvb, VBASE.
        -- unfold two62Z. rewrite EV in BV3. lia.
        -- rewrite Z.sub_diag. reflexivity.
  -
    destruct (exists_last (l:=lfst :: lrest) ltac:(discriminate)) as (ls0 & lp & ELP).
    rewrite ELP in *. clear ELP lfst lrest.
    set (ls := ls0 ++ [lp]) in *.
    assert (LSNE : ls <> []) by (subst ls; intros X; apply app_eq_nil in X; destruct X; discriminate).
    assert (INlp : In lp (u_levels g)) by (rewrite ELS; apply in_app_iff; left; subst ls; apply in_app_iff; right; left; reflexivity).
    assert (Vlp : level_valid lp) by exact (proj1 (Forall_forall _ _) LV lp INlp).
    pose proof Vlp as (VP1 & VP2 & VP3 & VP4 & VP5).
    assert (DLEN2 : u_D g = Z.of_nat (length ls0) + 2) by (rewrite DLEN; subst ls; rewrite length_app; cbn [length]; lia).
    pose proof (Zle_0_nat (length ls0)) as L0.

    set (wV := bv_add (ev E kVT) (wbv wm8)). set (wC := bv_add (ev E kCT) (wbv wm8)).
    set (wS := Z_to_bv 64 (lv_slot lp)). set (wT := Z_to_bv 64 (ctype_code (lv_t lp))). set (wR := Z_to_bv 64 (lv_rest lp)).
    set (nC := PrimInt63.add n 1) in *. set (nS := PrimInt63.add n 2) in *. set (nT := PrimInt63.add n 3) in *. set (nR := PrimInt63.add n 4) in *.
    set (E' := env_upd (env_upd (env_upd (env_upd (env_upd E n wV) nC wC) nS wS) nT wT) nR wR).
    assert (HX : env_ext n E E').
    { subst E'. eapply (env_ext_trans n nR); [lia| | apply env_upd_ext].
      eapply (env_ext_trans n nT); [lia| | apply env_upd_ext].
      eapply (env_ext_trans n nS); [lia| | apply env_upd_ext].
      eapply (env_ext_trans n nC); [lia| | apply env_upd_ext]. apply env_upd_ext. }
    assert (EVn : ev E' n = wV).
    { subst E'. rewrite !ev_upd_other by lia. apply env_upd_same. }
    assert (EVnC : ev E' nC = wC).
    { subst E'. rewrite 3!ev_upd_other by lia. apply env_upd_same. }
    assert (EVnS : ev E' nS = wS).
    { subst E'. rewrite 2!ev_upd_other by lia. apply env_upd_same. }
    assert (EVnT : ev E' nT = wT).
    { subst E'. rewrite 1!ev_upd_other by lia. apply env_upd_same. }
    assert (EVnR : ev E' nR = wR) by (subst E'; apply env_upd_same).
    pose proof (DRgen E' HX) as DR. pose proof (WDRgen E' HX) as WDR.
    assert (EVkVT : ev E' kVT = ev E kVT) by exact (ev_reval n E E' HX kVT ltac:(apply Uint63.ltb_spec; exact KVTn)).
    assert (EVkCT : ev E' kCT = ev E kCT) by exact (ev_reval n E E' HX kCT ltac:(apply Uint63.ltb_spec; exact KCTn)).
    clearbody E'.
    assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).

    assert (M8 : forall x, 8 <= bv_unsigned x -> bv_unsigned (bv_add x (wbv wm8)) = bv_unsigned x - 8).
    { intros x Hx. rewrite bv_add_unsigned, wbv_unsigned. unfold wm8. rewrite wsub_ok, wzero_ok, wlit_ok. change (to_Z 8%uint63) with 8.
      unfold bv_wrap. rewrite bv_modulus_64. pose proof (bv_unsigned_in_range _ x) as RK. rewrite bv_modulus_64 in RK. unfold two64 in *.
      change ((0 - 8) mod 18446744073709551616) with 18446744073709551608.
      replace (bv_unsigned x + 18446744073709551608) with (bv_unsigned x - 8 + 1 * 18446744073709551616) by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    assert (CE16 : v_begin (u_cstk g) + 16 <= v_end (u_cstk g)) by (unfold v_end; rewrite EC, SC, DLEN2; lia).
    assert (VE24 : v_begin (u_vstk g) + 24 <= v_end (u_vstk g)) by (unfold v_end; rewrite EV, SV', DLEN2; lia).
    assert (VBASE : bv_unsigned (ev E' n) = v_end (u_vstk g) - 16) by (rewrite EVn; subst wV; rewrite M8 by (rewrite KVTv; lia); rewrite KVTv; lia).
    assert (CBASE : bv_unsigned (ev E' nC) = v_end (u_cstk g) - 16) by (rewrite EVnC; subst wC; rewrite M8 by (rewrite KCTv; lia); rewrite KCTv; lia).

    destruct (level_block g LB lp P O INlp) as (chp & Hchp & OWNp & INBp).
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block chp) HA (proj1 O _ OWNp)) as (BP1 & BP2 & BP3 & BP4 & _).
    unfold chunk_block in BP1, BP2, BP3, INBp. cbn [fst snd] in BP1, BP2, BP3, INBp.
    pose proof (level_geom lp Vlp) as (GP1 & GP2 & GP3 & GP4 & GP5 & GP6).
    assert (SLOTR : 1 <= lv_slot lp /\ lv_slot lp + 24 < two64).
    { pose proof (INBp (lv_P lp) ltac:(unfold OBJ_SIZE in GP2; lia)) as I1. pose proof (INBp (lv_slot lp + 23) ltac:(unfold OBJ_SIZE in GP2; lia)) as I2.
      unfold in_iv in I1, I2. cbn [fst snd] in I1, I2. lia. }
    assert (SBASE : bv_unsigned (ev E' nS) = lv_slot lp) by (rewrite EVnS; subst wS; rewrite Z_to_bv_unsigned; apply bv_wrap_small; rewrite bv_modulus_64; lia).
    assert (TCODE : 0 <= ctype_code (lv_t lp) <= 2) by (destruct (lv_t lp); cbn; lia).
    assert (TBASE : bv_unsigned (ev E' nT) = ctype_code (lv_t lp)) by (rewrite EVnT; subst wT; rewrite Z_to_bv_unsigned; apply bv_wrap_small; rewrite bv_modulus_64; unfold two64; lia).
    assert (RBASE : bv_unsigned (ev E' nR) = lv_rest lp) by (rewrite EVnR; subst wR; rewrite Z_to_bv_unsigned; apply bv_wrap_small; rewrite bv_modulus_64; unfold two64, LIMIT in *; lia).

    pose proof M1 as CS1. rewrite ELS, removelast_snoc in CS1. subst ls. apply (proj1 (cstk_at_app _ _ _ _)) in CS1 as [_ CS1]. cbn [cstk_at] in CS1.
    destruct CS1 as (AT1 & AT2 & _).
    pose proof M3 as VS1. rewrite ELS, removelast_snoc in VS1. apply (proj1 (vstk_at_app _ _ _ _)) in VS1 as [_ VS1]. cbn [vstk_at] in VS1.
    destruct VS1 as [AV1 _].
    set (ls := ls0 ++ [lp]) in *.
    assert (CPOS : v_begin (u_cstk g) + 8 * Z.of_nat (length ls0) = v_end (u_cstk g) - 16) by (unfold v_end; rewrite EC, SC, DLEN2; lia).
    assert (VPOS : v_begin (u_vstk g) + 8 + 8 * Z.of_nat (length ls0) = v_end (u_vstk g) - 16) by (unfold v_end; rewrite EV, SV', DLEN2; lia).
    rewrite CPOS in AT1, AT2. rewrite VPOS in AV1.

    set (rC := region8 [Cell 0%uint63 4%uint63 (VP nT wzero); Cell 4%uint63 4%uint63 (VP nR wzero)]) in *.
    set (rV := region8 [Cell 0%uint63 8%uint63 (VP nS wzero)]) in *.
    assert (HIV8 : forall Ex, hiZ Ex rV = 8) by (intros; reflexivity). assert (LOV8 : loZ rV = 0) by reflexivity.
    assert (HIC8 : forall Ex, hiZ Ex rC = 8) by (intros; reflexivity). assert (LOC8 : loZ rC = 0) by reflexivity.
    set (wsB := ws0 ++ [top_win nC 8%uint63 2%uint63; top_win n 8%uint63 3%uint63]) in *.
    set (caB := [root; cb; VP nC (wlit 8%uint63); ccap; vb; VP n (wlit 8%uint63); vcap; zptr; zfree; c0; VP nS wzero; VP nT wzero; VP nR wzero; rootT; n1; P1; zh]) in *.
    assert (LENB : Z.of_nat (length wsB) < two63) by (subst wsB; rewrite length_app; cbn [length]; unfold two63; lia).
    assert (BYCn : forall a, v_end (u_cstk g) - 16 <= a < v_end (u_cstk g) - 8 ->
              (0 <= a /\ a + 1 < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws (map (wden E) ws) a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
    { intros a Ha. apply BYC. lia. }
    assert (BYVn : forall a, v_end (u_vstk g) - 16 <= a < v_end (u_vstk g) - 8 ->
              (0 <= a /\ a + 1 < two64) /\ ~ in_ivs IMGX a /\ ~ in_ws (map (wden E) ws) a /\ ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
    { intros a Ha. apply BYV. lia. }
    assert (NZC : PrimInt63.eqb nC 0%uint63 = false) by (apply (proj2 (Uint63.eqb_false_spec _ _)); intros X; assert (X' : to_Z nC = to_Z 0%uint63) by (rewrite X; reflexivity); change (to_Z 0%uint63) with 0 in X'; lia).
    assert (KRn : to_Z kR < to_Z n).
    { pose proof (VBo root (INCA root ltac:(left; reflexivity))) as X. unfold root in X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
    exists stB, E'. split; [right; reflexivity|]. split; [exact HX|]. subst stB.
    match goal with |- st_ok _ _ _ (setregs ?S1 (IMap.add _ _ ?R)) _ _ => change R with (s_regs S1) end.
    apply (GW.st_ok_subst_cells segs OPS E' _ ms model kR rR); [| | exact KR0|].
    2:{ cbn [surg s_regs]. assert (NDB : List.NoDup (map fst [(n, rV); (nC, rC)])).
        { cbn [map fst]. constructor; [intros [X|[]]; assert (X' := f_equal to_Z X); lia| constructor; [intros []| constructor]]. }
        apply (proj2 (find_add_regions _ _ kR rR (remove_keys_bst _ _ Pbst) NDB)).
        right. split; [cbn [map fst In]; intros [X|[X|[]]]; assert (X' := f_equal to_Z X); lia|].
        apply (proj2 (find_remove_keys _ _ kR rR Pbst)). split; [| exact FR].
        cbn [In]. intros [X|[X|[]]]; [rewrite X, Uint63.eqb_refl in KRC; discriminate| rewrite X, Uint63.eqb_refl in KRV; discriminate]. }
    2:{ intros v. destruct (sv_eqb v (VP kCT wzero)) eqn:QF1.
        - apply sv_eqb_eq in QF1. subst v. cbn [den]. rewrite EVnC, EVkCT. subst wC. apply add_m8_8.
        - destruct (sv_eqb v (VP kVT wzero)) eqn:QF2; [|reflexivity]. apply sv_eqb_eq in QF2. subst v. cbn [den]. rewrite EVn, EVkVT. subst wV. apply add_m8_8. }
    apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [kCT; kVT] [(n, rV); (nC, rC)] (mk_args 2%uint63 aw wsB caB) _ (PrimInt63.add n 5)).
    + exact KSall.
    + constructor; [| constructor; [intros []| constructor]]. cbn [map fst]. intros [X|[]]. apply (f_equal to_Z) in X. lia.
    + intros k r [H|[H|[]]]; injection H as <- <-; [exact NZ| exact NZC].
    +
      intros k r [H|[H|[]]]; injection H as <- <-.
      * apply (region_ok_fresh segs (s_priv st) E' (ms_mem ms) n rV NZ).
        -- cbn [rV region8 rg_cells]. apply IMap.bst_add. exact I.
        -- reflexivity.
        -- rewrite VBASE, LOV8. lia.
        -- rewrite VBASE, HIV8. destruct (BYVn (v_end (u_vstk g) - 9) ltac:(lia)) as (R & _). lia.
        -- intros a Ha. rewrite VBASE, LOV8, HIV8 in Ha. destruct (BYVn a ltac:(lia)) as (_ & _ & _ & MT & NSG). auto.
        -- intros gk gr F. cbn [rV region8 rg_cells] in F.
           destruct (Uint63.eqb gk 0) eqn:GK.
           ++ apply Uint63.eqb_correct in GK. subst gk. rewrite IMap.find_add_same in F by exact I. injection F as <-. cbn [g_cells].
              change (keyZ 0%uint63) with 0. rewrite Z.mul_0_r, Z.add_0_r. split.
              ** split; [cbn; tauto|]. constructor; [|constructor].
                 apply (cell_ok_of_u64 segs E' (ms_mem ms) (bv_unsigned (ev E' n)) 0%uint63 (VP nS wzero) (lv_slot lp)); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
                 --- change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, VBASE. exact AV1.
                 --- rewrite (den_VP0 E' nS wzero (weqb_refl _)). exact SBASE.
              ** intros c i [<-|[]] Hi. cbn [c_w c_idx] in Hi |- *. change (to_Z 8%uint63) with 8 in Hi. change (to_Z 0%uint63) with 0. rewrite LOV8, HIV8. lia.
           ++ apply Uint63.eqb_false_correct in GK. rewrite IMap.find_add_other in F by (try exact I; congruence). rewrite IMap.find_empty in F. discriminate.
      * apply (region_ok_fresh segs (s_priv st) E' (ms_mem ms) nC rC NZC).
        -- cbn [rC region8 rg_cells]. apply IMap.bst_add. exact I.
        -- reflexivity.
        -- rewrite CBASE, LOC8. lia.
        -- rewrite CBASE, HIC8. destruct (BYCn (v_end (u_cstk g) - 9) ltac:(lia)) as (R & _). lia.
        -- intros a Ha. rewrite CBASE, LOC8, HIC8 in Ha. destruct (BYCn a ltac:(lia)) as (_ & _ & _ & MT & NSG). auto.
        -- intros gk gr F. cbn [rC region8 rg_cells] in F.
           destruct (Uint63.eqb gk 0) eqn:GK.
           ++ apply Uint63.eqb_correct in GK. subst gk. rewrite IMap.find_add_same in F by exact I. injection F as <-. cbn [g_cells].
              change (keyZ 0%uint63) with 0. rewrite Z.mul_0_r, Z.add_0_r. split.
              ** split; [cbn; change (to_Z 0%uint63) with 0; change (to_Z 4%uint63) with 4; lia|]. constructor; [| constructor; [|constructor]].
                 --- apply (cell_ok_of_u32 segs E' (ms_mem ms) (bv_unsigned (ev E' nC)) 0%uint63 (VP nT wzero) (ctype_code (lv_t lp))); [change (to_Z 0%uint63) with 0; lia| change (to_Z 0%uint63) with 0; lia| |].
                     +++ change (to_Z 0%uint63) with 0. rewrite Z.add_0_r, CBASE. exact AT1.
                     +++ rewrite (den_VP0 E' nT wzero (weqb_refl _)), TBASE. apply Z.mod_small. lia.
                 --- apply (cell_ok_of_u32 segs E' (ms_mem ms) (bv_unsigned (ev E' nC)) 4%uint63 (VP nR wzero) (lv_rest lp)); [change (to_Z 4%uint63) with 4; lia| change (to_Z 4%uint63) with 4; lia| |].
                     +++ change (to_Z 4%uint63) with 4. rewrite CBASE. exact AT2.
                     +++ rewrite (den_VP0 E' nR wzero (weqb_refl _)), RBASE. apply Z.mod_small. unfold LIMIT in *. lia.
              ** intros c i [<-|[<-|[]]] Hi; cbn [c_w c_idx] in Hi |- *; [change (to_Z 4%uint63) with 4 in Hi; change (to_Z 0%uint63) with 0| change (to_Z 4%uint63) with 4 in Hi |- *]; rewrite LOC8, HIC8; lia.
           ++ apply Uint63.eqb_false_correct in GK. rewrite IMap.find_add_other in F by (try exact I; congruence). rewrite IMap.find_empty in F. discriminate.
    +
      intros k r a [H|[H|[]]] IR; injection H as <- <-; unfold inR in IR.
      * rewrite VBASE, LOV8, HIV8 in IR. destruct (BYVn a ltac:(lia)) as (RA & NI & NW & _). left. exact (FPold E' HX a ltac:(lia) NI NW).
      * rewrite CBASE, LOC8, HIC8 in IR. destruct (BYCn a ltac:(lia)) as (RA & NI & NW & _). left. exact (FPold E' HX a ltac:(lia) NI NW).
    +
      intros k1 r1 k2 r2 a H1 H2 NE12 [I1 I2]. pose proof (disj_cv g LB O) as DJ. unfold rdisj, v_bytes in DJ. rewrite EC, EV in DJ.
      assert (CAPC : v_end (u_cstk g) <= v_begin (u_cstk g) + 8 * v_cap (u_cstk g)) by (unfold v_end; rewrite EC; nia).
      assert (CAPV : v_end (u_vstk g) <= v_begin (u_vstk g) + 8 * v_cap (u_vstk g)) by (unfold v_end; rewrite EV; nia).
      destruct H1 as [H1|[H1|[]]]; destruct H2 as [H2|[H2|[]]]; injection H1 as <- <-; injection H2 as <- <-; try contradiction;
        unfold inR in I1, I2; rewrite ?VBASE, ?CBASE, ?LOV8, ?HIV8, ?LOC8, ?HIC8 in I1; rewrite ?VBASE, ?CBASE, ?LOV8, ?HIV8, ?LOC8, ?HIC8 in I2; lia.
    +
      rewrite (ho_holds _ _ _ _ _ HOPS).
      exists 2, (den E' aw), (map (wden E') wsB), (map (den E') caB), LB.
      split; [apply mk_args_sound; exact LENB|].

      split; [rewrite (DR aw INAW); apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); rewrite <- (WDR ws ltac:(auto));
              assert (WkE' : wins_ok 2 g (map (wden E') ws)) by (rewrite (WDR ws ltac:(auto)); exact Wk);
              apply (UOK.unp_wins_keep_map E' 2 g LB ws wsB P O WkE');
              [intros x Hx; subst wsB; apply in_app_or in Hx as [Hx|Hx]; [left; exact (proj1 (SUB0 x Hx))| right; left];
               destruct Hx as [<-|[<-|[]]]; apply UOK.kind_sub; vm_compute; reflexivity
              |intros x Hx; destruct (win3_eqb x (top_win kCT hc 2)) eqn:QK1;
               [right; left; apply win3_eqb_eq in QK1; subst x; apply UOK.kind_sub; vm_compute; reflexivity|];
               destruct (win3_eqb x (top_win kVT hv 3)) eqn:QK2;
               [right; left; apply win3_eqb_eq in QK2; subst x; apply UOK.kind_sub; vm_compute; reflexivity|];
               left; subst wsB; apply in_or_app; left; subst ws0; apply filter_In; split; [exact Hx|]; cbv beta; rewrite QK1, QK2; reflexivity]|]. split.
      *
        unfold windows_wf in *. subst wsB. rewrite map_app. apply Forall_app. split.
        -- rewrite (WDR ws0 ltac:(intros w Hw; exact (proj1 (SUB0 w Hw)))). apply Forall_forall. intros w Hw.
           apply in_map_iff in Hw as (x & <- & Hx). exact (proj1 (Forall_forall _ _) WF (wden E x) (in_map _ _ _ (proj1 (SUB0 x Hx)))).
        -- assert (CAPC : v_end (u_cstk g) <= v_begin (u_cstk g) + 8 * v_cap (u_cstk g)) by (unfold v_end; rewrite EC; nia).
           assert (CAPV : v_end (u_vstk g) <= v_begin (u_vstk g) + 8 * v_cap (u_vstk g)) by (unfold v_end; rewrite EV; nia).
           constructor; [| constructor; [|constructor]]; rewrite top_win_den; [rewrite CBASE| rewrite VBASE]; unfold window_wf; cbn [w_lo w_len w_kind w_iv];
             change (to_Z 8%uint63) with 8.
           ++ change (to_Z 2%uint63) with 2. split; [lia|]. split; [lia|]. split; [unfold two64 in *; lia|].
              right; right. split; [unfold K_SUB; lia|]. exists (cstk_block g). split; [exact (proj1 O _ OWC)|].
              intros a Ha. unfold in_iv, cstk_block, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. unfold v_bytes. rewrite EC. lia.
           ++ change (to_Z 3%uint63) with 3. split; [lia|]. split; [lia|]. split; [unfold two64 in *; lia|].
              right; right. split; [unfold K_SUB; lia|]. exists (vstk_block g). split; [exact (proj1 O _ OWV)|].
              intros a Ha. unfold in_iv, vstk_block, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. unfold v_bytes. rewrite EV. lia.
      *
        cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. subst caB. cbn [map decode_uc].
        set (gB := mkUnp (u_ctx g) (u_vis g) (u_data g) (u_len g) ls (vec_pop (u_cstk g)) (vec_pop (u_vstk g)) (u_zone g)).
        destruct (vec_pop_valid (u_cstk g) VC ltac:(rewrite SC, DLEN2; lia)) as [VCP CEP].
        destruct (vec_pop_valid (u_vstk g) VV ltac:(rewrite SV', DLEN2; lia)) as [VVP VEP].
        rewrite EC in CEP. rewrite EV in VEP.
        assert (UDB : u_D gB = Z.of_nat (length ls0) + 1) by (unfold u_D; cbn [u_levels gB]; subst ls; rewrite length_app; cbn [length]; lia).
        assert (CURB : u_cur_slot gB = lv_slot lp) by (unfold u_cur_slot; cbn [u_levels gB]; change (u_root gB) with (u_root g); subst ls; apply cur_slot_snoc).
        assert (LASTB : last_opt ls = Some lp) by (subst ls; unfold last_opt; rewrite rev_app_distr; reflexivity).
        exists gB. split; [| split; [| split; [| split; [| split; [| split]]]]].
        --
           unfold link. cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1].
           change (u_root gB) with (u_root g). change (u_cstk gB) with (vec_pop (u_cstk g)). change (u_vstk gB) with (vec_pop (u_vstk g)).
           change (u_zone gB) with (u_zone g). change (u_levels gB) with ls.
           rewrite (DR root), (DR cb), (DR ccap), (DR vb), (DR vcap), (DR zptr), (DR zfree), (DR c0), (DR rootT), (DR n1), (DR P1) by (apply INCA; inlist).
           rewrite CEP, VEP.
           change (v_begin (vec_pop (u_cstk g))) with (v_begin (u_cstk g)). change (v_begin (vec_pop (u_vstk g))) with (v_begin (u_vstk g)).
           change (v_capend (vec_pop (u_cstk g))) with (v_capend (u_cstk g)). change (v_capend (vec_pop (u_vstk g))) with (v_capend (u_vstk g)).
           split; [exact Lroot|]. split; [exact Lcb|].
           split; [cbn [den]; rewrite bv_add_unsigned, wbv_unsigned, wlit_ok, CBASE; change (to_Z 8%uint63) with 8; unfold bv_wrap; rewrite bv_modulus_64, Z.mod_small by (unfold two64 in *; lia); lia|].
           split; [exact Lccap|]. split; [exact Lvb|].
           split; [cbn [den]; rewrite bv_add_unsigned, wbv_unsigned, wlit_ok, VBASE; change (to_Z 8%uint63) with 8; unfold bv_wrap; rewrite bv_modulus_64, Z.mod_small by (unfold two64 in *; lia); lia|].
           split; [exact Lvcap|]. split; [exact Lzp|]. split; [exact Lzf|]. split; [exact Lc0|].
           intros _. split; [| split].
           ++ rewrite CURB, (den_VP0 E' nS wzero (weqb_refl _)), SBASE. reflexivity.
           ++ exists lp. split; [exact LASTB|]. rewrite (den_VP0 E' nT wzero (weqb_refl _)), (den_VP0 E' nR wzero (weqb_refl _)), TBASE, RBASE. auto.
           ++ rewrite ELS in E1. destruct ls0 as [|l0 ls0'].
              --- exists lp, []. split; [reflexivity|]. cbn [app] in E1. subst ls. cbn [app] in E1. injection E1 as <- <-. auto.
              --- exists l0, (ls0' ++ [lp]). subst ls. cbn [app] in E1 |- *. injection E1 as <- <-. split; [reflexivity|]. auto.
        --
           unfold pure_ok. change (u_cstk gB) with (vec_pop (u_cstk g)). change (u_vstk gB) with (vec_pop (u_vstk g)).
           change (u_zone gB) with (u_zone g). change (u_levels gB) with ls. rewrite UDB.
           change (v_elt (vec_pop (u_cstk g))) with (v_elt (u_cstk g)). change (v_elt (vec_pop (u_vstk g))) with (v_elt (u_vstk g)).
           change (v_size (vec_pop (u_cstk g))) with (v_size (u_cstk g) - 1). change (v_size (vec_pop (u_vstk g))) with (v_size (u_vstk g) - 1).
           change (v_cap (vec_pop (u_cstk g))) with (v_cap (u_cstk g)). change (v_cap (vec_pop (u_vstk g))) with (v_cap (u_vstk g)).
           rewrite SC, SV', DLEN2.
           split; [exact VCP|]. split; [exact EC|]. split; [lia|]. split; [exact Q4|]. split; [exact VVP|]. split; [exact EV|]. split; [lia|]. split; [exact Q8|].
           split; [exact Vls|]. split; [rewrite DLEN2 in Q10; lia|]. split; [exact LAls| exact Q12].
        --   exact O.
        --
           unfold wins_ok in *. subst wsB. rewrite map_app. apply Forall_app. split.
           ++ rewrite (WDR ws0 ltac:(intros w Hw; exact (proj1 (SUB0 w Hw)))). apply Forall_forall. intros w Hw NS.
              apply in_map_iff in Hw as (x & <- & Hx). destruct (SUB0 x Hx) as (Hx0 & _ & _).
              destruct (proj1 (Forall_forall _ _) Wk (wden E x) (in_map _ _ _ Hx0) NS) as [DJ|[NB SO]]; [left; exact DJ| right].
              split; [exact NB|]. unfold sub_ok in SO |- *. cbv zeta in SO |- *.
              change (u_cstk gB) with (vec_pop (u_cstk g)). change (u_vstk gB) with (vec_pop (u_vstk g)). change (u_zone gB) with (u_zone g). change (u_levels gB) with ls.
              rewrite CEP, VEP. change (v_begin (vec_pop (u_cstk g))) with (v_begin (u_cstk g)). change (v_begin (vec_pop (u_vstk g))) with (v_begin (u_vstk g)).
              change (v_capend (vec_pop (u_cstk g))) with (v_capend (u_cstk g)). change (v_capend (vec_pop (u_vstk g))) with (v_capend (u_vstk g)).
              destruct SO as [(KK & A1 & A2 & A3)|[(KK & A1 & A2 & A3)|[(KK & _)|A]]];
                [left; repeat split; auto; lia| right; left; repeat split; auto; lia| exfalso; exact (NSL _ (in_map _ _ _ Hx0) KK)| right; right; right; exact A].
           ++ assert (CAPC : v_end (u_cstk g) <= v_capend (u_cstk g)) by (unfold v_end, v_capend; rewrite EC; nia).
              assert (CAPV : v_end (u_vstk g) <= v_capend (u_vstk g)) by (unfold v_end, v_capend; rewrite EV; nia).
              constructor; [| constructor; [|constructor]].
              ** intros _. right. rewrite top_win_den, CBASE. split; [cbn [w_kind]; unfold K_BLOCK; change (to_Z 2%uint63) with 2; lia|].
                 unfold sub_ok; cbv zeta; cbn [w_kind w_lo w_len]; change (to_Z 8%uint63) with 8. change (to_Z 2%uint63) with 2.
                 change (u_cstk gB) with (vec_pop (u_cstk g)). rewrite CEP.
                 change (v_begin (vec_pop (u_cstk g))) with (v_begin (u_cstk g)). change (v_capend (vec_pop (u_cstk g))) with (v_capend (u_cstk g)).
                 left. split; [reflexivity|]. lia.
              ** intros _. right. rewrite top_win_den, VBASE. split; [cbn [w_kind]; unfold K_BLOCK; change (to_Z 3%uint63) with 3; lia|].
                 unfold sub_ok; cbv zeta; cbn [w_kind w_lo w_len]; change (to_Z 8%uint63) with 8. change (to_Z 3%uint63) with 3.
                 change (u_vstk gB) with (vec_pop (u_vstk g)). rewrite VEP.
                 change (v_begin (vec_pop (u_vstk g))) with (v_begin (u_vstk g)). change (v_capend (vec_pop (u_vstk g))) with (v_capend (u_vstk g)).
                 right; left. split; [reflexivity|]. lia.
        --
           unfold mem_ok. cbv zeta. change (u_levels gB) with ls. change (u_zone gB) with (u_zone g). change (u_root gB) with (u_root g).
           change (u_cstk gB) with (vec_pop (u_cstk g)). change (u_vstk gB) with (vec_pop (u_vstk g)).
           change (v_begin (vec_pop (u_cstk g))) with (v_begin (u_cstk g)). change (v_begin (vec_pop (u_vstk g))) with (v_begin (u_vstk g)).
           pose proof M1 as CS2. rewrite ELS, removelast_snoc in CS2. pose proof M3 as VS2. rewrite ELS, removelast_snoc in VS2.
           assert (RL : removelast ls = ls0) by (subst ls; apply removelast_snoc).
           rewrite RL.
           split; [subst ls; exact (proj1 (proj1 (cstk_at_app _ _ _ _) CS2))|].
           split; [intros _; exact (M2 NE)|].
           split; [subst ls; exact (proj1 (proj1 (vstk_at_app _ _ _ _) VS2))|].
           split; [exact M4|]. split; [| exact CWls].

           pose proof M5 as CT5. rewrite ELS in CT5. subst ls.
           destruct ls0 as [|l0 ls0'].
           ++ cbn. exact I.
           ++ cbn [app] in CT5 |- *. cbn [containers tl] in CT5 |- *.
              rewrite containers_app in CT5. cbn [containers] in CT5.
              apply (proj1 (conts_at_app _ _ _ _ _ (containers_length _ _))) in CT5 as [CT5 _]. exact CT5.
        --
           intros _. cbv zeta. change (u_levels gB) with ls. change (u_zone gB) with (u_zone g). rewrite CURB.
           cbn [c_rootT c_n1 c_P1].
           exists oc. split; [exact OTW|]. split; [exact OKA|]. split; [| split; [intros X; exfalso; exact (LSNE X)| split; [| split; [exact OBOD| split; [exact DEPC|]]]]].
           3:{ exists S1. split; [exact KP1|]. apply (POTgen E' wsB (WDR ws ltac:(auto))).
               intros x Hx. subst wsB. apply in_app_or in Hx as [Hx|[<-|[<-|[]]]]; [left; exact (proj1 (SUB0 x Hx))| right; apply kind_ne; vm_compute; reflexivity| right; apply kind_ne; vm_compute; reflexivity]. }
           ++ intros _.
              assert (ATM : u32_at (bmem_of segs (ms_mem ms)) (cur_slot (u_root g) ls) (container_type (lv_t l)) /\
                            u32_at (bmem_of segs (ms_mem ms)) (cur_slot (u_root g) ls + 8) (lv_n l) /\
                            u64_at (bmem_of segs (ms_mem ms)) (cur_slot (u_root g) ls + 16) (lv_P l)).
              { pose proof M5 as CT5. rewrite ELS in CT5. subst ls. destruct ls0 as [|l0 ls0'].
                - cbn [app containers tl conts_at] in CT5. cbn [app]. unfold cur_slot. cbn [rev app]. tauto.
                - cbn [app] in CT5 |- *. cbn [containers tl] in CT5. rewrite containers_app in CT5. cbn [containers] in CT5.
                  apply (proj1 (conts_at_app _ _ _ _ _ (containers_length _ _))) in CT5 as [_ CT5]. cbn [conts_at] in CT5.
                  rewrite cur_slot_cons. tauto. }
              destruct ATM as (A1 & A2 & A3). pose proof (OHD A1 A2 A3) as HD. subst ls. rewrite cur_slot_snoc in HD. exact HD.
           ++ pose proof OCELLS as OC. subst ls. rewrite cur_slot_snoc in OC. exact OC.
        --   split; [split; [change (u_levels gB) with ls; change (u_zone gB) with (u_zone g); exact AXls| intros X; discriminate X]|].

           change (u_zone gB) with (u_zone g). subst wsB. rewrite map_app. apply SealX.seal_ok_app_other.
           ++ rewrite (WDR ws0 ltac:(intros w Hw; exact (proj1 (SUB0 w Hw)))). apply (SealX.seal_ok_map _ _ _ _ _ SE). intros x Hx. left. exact (proj1 (SUB0 x Hx)).
           ++ intros w [<-|[<-|[]]]; apply kind_ne; vm_compute; reflexivity.
    +
      intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
      apply (proj1 (heap_fp_iff IMGX _ 2 _ (map (wden E') wsB) _ a (mk_args_sound E' 2%uint63 aw _ _ LENB))) in FPa as (RA & NI & NW).
      subst wsB. rewrite map_app in NW. split.
      * destruct (in_ws_dec (map (wden E') ws) a) as [IN|NIN].
        -- right. apply (REMOVED E' HX a IN). intros X. apply NW. unfold in_ws in *. rewrite map_app. apply (proj2 (in_ivs_app _ _ _)). left. exact X.
        -- left. rewrite (WDR ws ltac:(auto)) in NIN. exact (FPold E' HX a RA NI NIN).
      * intros k r [H|[H|[]]] IR; injection H as <- <-; apply NW; unfold in_ws; rewrite map_app; apply (proj2 (in_ivs_app _ _ _)); right;
          cbn [map]; rewrite !top_win_den; unfold in_ivs; unfold inR in IR; rewrite ?LOV8, ?HIV8, ?LOC8, ?HIC8 in IR; change (to_Z 8%uint63) with 8.
        -- apply Exists_cons_tl. constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. lia.
        -- constructor. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. lia.
    +
      assert (FH' : facts_hold E' (s_facts st)) by exact (so_facts _ _ _ _ _ _ HS).
      cbn [app]. repeat match goal with |- Forall _ (_ :: _) => constructor | |- Forall _ (_ ++ _) => apply Forall_app; split end.
      * cbn [fact_holds]. rewrite (DR cb (INCA cb ltac:(right; left; reflexivity))). intros X.
        assert (X' : bv_unsigned (den E cb) = bv_unsigned (den E' (VP kCT wzero))) by (rewrite X; reflexivity).
        rewrite (den_VP0 E' kCT wzero (weqb_refl _)), EVkCT, KCTv, <- Lcb in X'. lia.
      * cbn [fact_holds]. rewrite (DR cb (INCA cb ltac:(right; left; reflexivity))), <- Lcb. cbn [den].
        rewrite bv_add_unsigned, wbv_unsigned, wlit_ok, CBASE. change (to_Z 8%uint63) with 8. unfold bv_wrap. rewrite bv_modulus_64, Z.mod_small by (unfold two64 in *; lia). lia.
      * cbn [fact_holds den]. rewrite EVkVT. fold wV. rewrite <- EVn. apply bv_eq. exact (den_VP0 E' n wzero (weqb_refl _)).
      * cbn [fact_holds den]. rewrite EVkCT. fold wC. rewrite <- EVnC. apply bv_eq. exact (den_VP0 E' nC wzero (weqb_refl _)).
      * cbn [fact_holds]. rewrite TBASE, wzero_ok, wlit_ok. change (to_Z 2%uint63) with 2. lia.
      * cbn [fact_holds]. rewrite RBASE, wone_ok, wlit_ok. change (to_Z 1000%uint63) with 1000. unfold LIMIT in *. lia.
      * cbn [fact_holds]. rewrite SBASE, wone_ok, wsub_ok, wzero_ok, wlit_ok. change ((0 - to_Z 25%uint63) mod two64) with 18446744073709551591. unfold two64 in *. lia.
      * cbn [fact_holds]. rewrite SBASE. change (2 ^ to_Z 3%uint63) with 8. unfold lv_slot, OBJ_SIZE.
        replace (lv_P lp + 24 * lv_k lp) with (lv_P lp + (3 * lv_k lp) * 8) by lia. rewrite Z_mod_plus_full. exact VP5.
      * pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold Mem.two62Z in CEIL.
        apply GW.top_facts_sound; [exact FH'| |];
          rewrite (DR vb (INCA vb ltac:(do 4 right; left; reflexivity))), <- Lvb, VBASE.
        -- unfold two62Z. rewrite EV in BV3. unfold v_end in *. rewrite EV in *. lia.
        -- unfold v_end. rewrite EV. replace (v_begin (u_vstk g) + 8 * v_size (u_vstk g) - 16 - v_begin (u_vstk g)) with ((v_size (u_vstk g) - 2) * 8) by lia.
           apply Z_mod_mult.
      * pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold Mem.two62Z in CEIL.
        apply GW.top_facts_sound; [exact FH'| |];
          rewrite (DR cb (INCA cb ltac:(right; left; reflexivity))), <- Lcb, CBASE.
        -- unfold two62Z. rewrite EC in BC3. unfold v_end in *. rewrite EC in *. lia.
        -- unfold v_end. rewrite EC. replace (v_begin (u_cstk g) + 8 * v_size (u_cstk g) - 16 - v_begin (u_cstk g)) with ((v_size (u_cstk g) - 2) * 8) by lia.
           apply Z_mod_mult.
Qed.

Theorem g3p_sound : contract_sound segs OPS MP PB g3p_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [g3p_contract c_apply] in HAP.
  destruct (g3p_apply st) as [[|stA [|stB [|? ?]]]|] eqn:AP; try discriminate.
  3: { injection HAP as <-. destruct (g3p_sound_main E st ms model stA stB HS AP) as (st' & E' & OR & HX & HS').
       apply (Hk st' ltac:(destruct OR as [-> | ->]; [left; reflexivity| right; left; reflexivity]) E' ms model HX HMP HS'). }
  all: exfalso; unfold g3p_apply in AP;
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound2.
End WithPc2.
End G3P.
