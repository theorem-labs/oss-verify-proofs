(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp GWin.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU.
Open Scope Z_scope.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GExcl.

Definition half (oc : w64) : option w64 :=
  if wt oc then None else
  let h := PrimInt63.lsr (wl oc) 1%uint63 in
  if PrimInt63.eqb (PrimInt63.add h h) (wl oc) && PrimInt63.ltb h bit62i then Some (wlit h) else None.

Lemma half_ok : forall oc h, half oc = Some h -> w2Z oc = 2 * w2Z h /\ 0 <= w2Z h < 2 ^ 62.
Proof.
  intros oc h H. unfold half in H. destruct (wt oc) eqn:T; [discriminate|].
  set (x := PrimInt63.lsr (wl oc) 1%uint63) in *.
  destruct (PrimInt63.eqb (PrimInt63.add x x) (wl oc) && PrimInt63.ltb x bit62i) eqn:C; [|discriminate].
  injection H as <-. apply andb_prop in C as [C1 C2].
  apply Uint63.eqb_correct in C1. apply Uint63.ltb_spec in C2. change (to_Z bit62i) with (2 ^ 62) in C2.
  pose proof (to_Z_bounded x) as BX. rewrite wlit_ok. split; [|lia].
  unfold w2Z. rewrite T. rewrite <- C1, Uint63.add_spec. change wB with (2 ^ 63).
  rewrite Z.mod_small by lia. lia.
Qed.

Definition implied2 (fs : list fact) (f : fact) : bool :=
  let vs := fact_vs f in
  if implied (rel_facts vs fs) f then true else implied (rel_facts (close_vs fs vs vs) fs) f.
Lemma implied2_sound : forall E fs f, ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E fs -> implied2 fs f = true -> fact_holds E f.
Proof.
  intros E fs f Hz FH H. unfold implied2 in H. cbv zeta in H.
  destruct (implied (rel_facts (fact_vs f) fs) f) eqn:I1.
  - exact (implied_sound E _ f Hz (rel_facts_hold E _ fs FH) I1).
  - exact (implied_sound E _ f Hz (rel_facts_hold E _ fs FH) H).
Qed.

Section WithPc.
Variable EXCL_PC : int.

Definition gexcl_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 then
        match ca with
        | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
            match vb, vcap with
            | VP kB ob, VP kB' oc =>
                match half oc with
                | Some h =>
                    if weqb ob wzero && PrimInt63.eqb kB kB' && implied2 (s_facts st) (FULe ve (VP kB h))
                    then Some [addfact st (FULt ce ccap)] else None
                | None => None
                end
            | _, _ => None
            end
        | _ => None
        end
      else None
  | None => None
  end.

Definition gexcl_contract : contract := Contract EXCL_PC gexcl_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma gexcl_fact : forall E st ms model aw ws root cb ce ccap vb ve vcap zptr zfree c0 slot tD restD rootT n1 P1 zh kB ob oc h,
  st_ok segs OPS E st ms model ->
  the_op st = Some (1%uint63, aw, ws, [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]) ->
  vb = VP kB ob -> vcap = VP kB oc -> weqb ob wzero = true -> half oc = Some h ->
  implied2 (s_facts st) (FULe ve (VP kB h)) = true ->
  fact_holds E (FULt ce ccap).
Proof.
  intros E st ms model aw ws root cb ce ccap vb ve vcap zptr zfree c0 slot tD restD rootT n1 P1 zh kB ob oc h HS TO EVB EVC OB HH IMP.
  pose proof (so_ops _ _ _ _ _ _ HS) as Pops. pose proof (so_zero _ _ _ _ _ _ HS) as Pz. pose proof (so_facts _ _ _ _ _ _ HS) as Pfacts.
  pose proof (implied2_sound E (s_facts st) _ Pz Pfacts IMP) as I1. cbn [fact_holds] in I1.
  destruct (the_op_sound E st 1%uint63 aw ws _ TO) as (o & OPS1 & OID & DEC & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (mdZ & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC). rewrite DEC in DEC0. injection DEC0 as <- <- <- <-.
  change (to_Z 1%uint63) with 1 in HC.
  cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC.
  cbn [map decode_uc] in HC.
  destruct HC as (g & L & P & O & _).
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & _).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap] in Lcb, Lce, Lccap, Lvb, Lve, Lvcap.
  pose proof P as (VC & EC & SC & CC & VV & EV & SV' & CV & _).
  pose proof (own_tied g LB O) as TIE. unfold v_bytes in TIE. rewrite EC, EV in TIE.
  destruct O as [OIN _].

  assert (BV : 4096 <= v_begin (u_vstk g) /\ v_begin (u_vstk g) + 8 * v_cap (u_vstk g) <= two62Z).
  { assert (IN : In (v_begin (u_vstk g), v_bytes (u_vstk g)) LB).
    { apply OIN. unfold owned, cstk_block, vstk_block. cbn [In]. tauto. }
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA IN) as (B1 & B2 & B3 & B4 & _).
    pose proof (aw_blocks_lo segs IMGX AW _ LB _ (ms_mem ms) model _ HA IN) as B5.
    pose proof (aw_ceiling_small segs IMGX AW model) as B6.
    cbn [fst snd] in B1, B2, B3, B5. unfold v_bytes in B3. rewrite EV in B3. unfold two62Z in *. lia. }
  destruct VC as (_ & VC2 & _). destruct VV as (_ & VV2 & _).
  destruct (half_ok oc h HH) as [OC HR].
  pose proof two64_eq as T64. pose proof (evk_range E kB) as RK.
  assert (H62 : two62Z = 2 ^ 62) by reflexivity.

  subst vb vcap. rewrite (den_VP0 E kB ob OB) in Lvb.

  assert (CAPV : 8 * v_cap (u_vstk g) = w2Z oc).
  { unfold v_capend in Lvcap. rewrite EV, den_VPu, Lvb in Lvcap.
    rewrite Z.mod_small in Lvcap by (rewrite T64; lia). lia. }

  assert (SZV : 8 * v_size (u_vstk g) <= w2Z h).
  { unfold v_end in Lve. rewrite EV in Lve. rewrite den_VPu in I1.
    rewrite Z.mod_small in I1 by (rewrite T64; lia). lia. }

  cbn [fact_holds]. rewrite <- Lce, <- Lccap. unfold v_end, v_capend. rewrite EC. lia.
Qed.

Theorem gexcl_sound : contract_sound segs OPS MP PB gexcl_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [gexcl_contract c_apply] in HA. unfold gexcl_apply in HA.
  destruct (the_op st) as [[[[md aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb md 1%uint63) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst md.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate HA.
  destruct vb as [|kB ob| | | | | | | | |]; try discriminate HA.
  destruct vcap as [|kB' oc| | | | | | | | |]; try discriminate HA.
  destruct (half oc) as [h|] eqn:HH; [|discriminate].
  match type of HA with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection HA as <-.
  apply andb_prop in COND as [COND IMP]. apply andb_prop in COND as [OB KK]. apply Uint63.eqb_correct in KK. subst kB'.
  assert (OK' : st_ok segs OPS E (addfact st (FULt ce ccap)) ms model).
  { apply (addfact_sound segs OPS); [exact HS|].
    exact (gexcl_fact E st ms model aw ws root cb ce ccap _ ve _ zptr zfree c0 slot tD restD rootT n1 P1 zh kB ob oc h HS TO eq_refl eq_refl OB HH IMP). }
  exact (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next (addfact st (FULt ce ccap))) E) HMP OK').
Qed.

End Sound.
End WithPc.
End GExcl.
