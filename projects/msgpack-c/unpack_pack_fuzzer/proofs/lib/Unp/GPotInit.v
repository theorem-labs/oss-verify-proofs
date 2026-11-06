(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Pot GPot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Ops GLib GUnp.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GPotInit.

Section WithPc.
Variable INIT_PC : int.

Definition gpotinit_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 then
      match ca with
      | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
          let n := s_next st in
          if sv_eqb cb ce && st_vars_below n st && PrimInt63.ltb 0%uint63 n && Z.ltb (Z.of_nat (length ws)) 4096
             && GPot.GPot.all_not_pot (s_facts st) ws
          then Some [surg st [] [] (mk_args 1%uint63 aw (ws ++ [GPot.GPot.pw n]) ca) (GPot.GPot.pot_facts_init n) (PrimInt63.add n 1%uint63)]
          else None
      | _ => None
      end
      else None
  | None => None
  end.

Definition gpotinit_contract : contract := Contract INIT_PC gpotinit_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma gpotinit_apply_sound : forall E st ms model st',
  st_ok segs OPS E st ms model -> gpotinit_apply st = Some [st'] ->
  exists E', env_ext (s_next st) E E' /\ st_ok segs OPS E' st' ms model.
Proof.
  intros E st ms model st' HS0 AP.
  unfold gpotinit_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection AP as <-.
  apply andb_prop in COND as [COND NOPOT]. apply andb_prop in COND as [COND WLEN]. apply Z.ltb_lt in WLEN.
  apply andb_prop in COND as [COND NPOS]. apply andb_prop in COND as [CBCE VB]. apply sv_eqb_eq in CBCE. subst ce.
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS.
  set (n := s_next st) in *.

  set (E' := env_upd E n (wbv GPot.GPot.Q0w)).
  assert (HX : env_ext n E E') by apply env_upd_ext.
  exists E'. split; [exact HX|].
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
  clear HS0.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (EVn : bv_unsigned (ev E' n) = Pot.Pot.Q0) by (subst E'; rewrite env_upd_same, wbv_unsigned; reflexivity).
  clearbody E'.

  destruct (the_op_full st 1%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E') as DEC.
  rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 1%uint63) with 1 in HC.
  cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC.
  cbn [map decode_uc] in HC.
  destruct HC as (g & L & P & O & Wk & M & CS0 & [AX PTU] & SE).
  pose proof L as (Lroot & Lcb & Lce & _).
  cbn [c_cb c_ce] in Lcb, Lce.
  pose proof P as (VC & EC & SC & _).

  assert (NIL : u_levels g = []).
  { assert (X : v_begin (u_cstk g) = v_end (u_cstk g)) by (rewrite Lcb, Lce; reflexivity).
    unfold v_end in X. rewrite EC, SC in X. unfold u_D in X. destruct (u_levels g); [reflexivity| cbn [length] in X; lia]. }

  assert (NOP : forall x, In x ws -> ~ pot_win (wden E' x)).
  { intros x Hx. exact (GPot.GPot.not_pot_sound E' (s_facts st) x Pfacts (GPot.GPot.all_not_pot_In _ _ NOPOT x Hx)). }
  assert (Q41 : bv_unsigned (ev E' n) <= 2 ^ 41) by (rewrite EVn; unfold Pot.Pot.Q0; lia).
  assert (PWD : wden E' (GPot.GPot.pw n) = Win (POT_BASE + Pot.Pot.Q0) 0 K_STACK).
  { unfold GPot.GPot.pw. rewrite GPot.GPot.pwl_den, (GPot.GPot.pw_den_lo E' n Q41), EVn. reflexivity. }
  assert (LEN' : Z.of_nat (length (ws ++ [GPot.GPot.pw n])) < two63).
  { rewrite length_app. cbn [length]. unfold two63. lia. }

  apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [] [] (mk_args 1%uint63 aw (ws ++ [GPot.GPot.pw n]) _) _ (PrimInt63.add n 1)).
  - intros k [].
  - constructor.
  - intros k r [].
  - intros k r [].
  - intros k r a [].
  - intros k1 r1 k2 r2 a [].
  -
    rewrite (ho_holds _ _ _ _ _ HOPS).
    exists 1, (den E' aw), (map (wden E') (ws ++ [GPot.GPot.pw n])), (map (den E') [root; cb; cb; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]), LB.
    split; [apply mk_args_sound; exact LEN'|].
    split; [apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); rewrite map_app; apply wins_keep_app; intros w0 [<-|[]]; rewrite PWD; split;
            [apply UOK.pseudo_untied; split; [reflexivity| cbn [w_lo]; unfold AW_BAND, POT_BASE, Pot.Pot.Q0; lia]| cbn [w_kind]; unfold K_STACK, K_BLOCK; lia]|]. split.
    +
      unfold windows_wf in *. rewrite map_app. apply Forall_app. split; [exact WF|]. constructor; [|constructor].
      rewrite PWD. unfold window_wf. cbn [w_lo w_len w_kind]. pose proof (aw_ceiling_small segs IMGX AW model) as CEIL.
      unfold POT_BASE, Pot.Pot.Q0, Mem.two62Z, two64 in *. split; [lia|]. split; [lia|]. split; [lia|]. left. split; [reflexivity| lia].
    +
      cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. cbn [map decode_uc].
      exists g. split; [exact L|]. split; [exact P|]. split; [exact O|]. split; [| split; [exact M| split; [intros X; discriminate X| split; [split; [exact AX|]|]]]].
      * unfold wins_ok in *. rewrite map_app. apply Forall_app. split; [exact Wk|]. constructor; [|constructor].
        intros NK. exfalso. apply NK. rewrite PWD. reflexivity.
      *
        intros MD1. destruct (PTU MD1) as (S0 & KP0 & _). exists S0. split; [exact KP0|]. rewrite NIL in KP0 |- *.
        rewrite (Pot.Pot.kids_pk_nil_inv _ _ _ KP0), Pot.Pot.pot_val_nil. intros w Hw PW. rewrite map_app in Hw. apply in_app_or in Hw as [Hw|[<-|[]]].
        -- exfalso. apply in_map_iff in Hw as (x & <- & Hx). exact (NOP x Hx PW).
        -- rewrite PWD. cbn [w_lo]. lia.
      * rewrite map_app. apply SealX.seal_ok_app_other; [exact SE|]. intros w [<-|[]]. rewrite PWD. cbn [w_kind]. unfold Seal.K_TWIN, K_STACK. lia.
  -
    intros a FPa. split; [| intros k r []]. left. unfold FP in FPa |- *. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa |- *.
    apply (proj1 (heap_fp_iff IMGX _ 1 _ (map (wden E') (ws ++ [GPot.GPot.pw n])) _ a (mk_args_sound E' 1%uint63 aw _ _ LEN'))) in FPa as (RA & NI & NW).
    apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E') ws) _ a DEC)). split; [exact RA|]. split; [exact NI|].
    intros X. apply NW. unfold in_ws in *. rewrite !map_app. apply in_ivs_app. left. exact X.
  -
    unfold GPot.GPot.pot_facts_init. constructor; [| constructor; [| constructor]].
    + cbn [fact_holds]. apply bv_eq. rewrite (den_VP0 E' n wzero (weqb_refl _)), EVn, den_VL, GPot.GPot.Q0w_ok. reflexivity.
    + cbn [fact_holds]. rewrite EVn, wzero_ok, GPot.GPot.FXMAXw_ok. unfold Pot.Pot.Q0. lia.
Qed.

Theorem gpotinit_sound : contract_sound segs OPS MP PB gpotinit_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [gpotinit_contract c_apply] in HAP.
  destruct (gpotinit_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  - exfalso. unfold gpotinit_apply in AP.
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
  - injection HAP as <-. destruct (gpotinit_apply_sound E st ms model st' HS AP) as (E' & HX & HS').
    exact (Hk st' (or_introl eq_refl) E' ms model HX HMP HS').
  - exfalso. unfold gpotinit_apply in AP.
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End WithPc.
End GPotInit.
