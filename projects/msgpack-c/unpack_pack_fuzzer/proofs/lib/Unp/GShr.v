(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Ops GLib GUnp GRoom GWin.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GShr.

Definition shrink8 (r : region) : region :=
  Region (rg_lo r) (VL (wlit 8%uint63)) (rg_w r) (rg_bg r) (IMap.remove 1%uint63 (rg_cells r)).

Definition same_end (fs : list fact) (v t : sv) : bool :=
  sv_eqb v t
  || match v, t with
     | VP k o, VP kt ot => fact_lookup fs (is_FEq (VP kt wzero) (VP k (wsub o ot)))
     | _, _ => false
     end.

Lemma same_end_sound : forall E fs v t, facts_hold E fs -> same_end fs v t = true -> den E v = den E t.
Proof.
  intros E fs v t FH H. unfold same_end in H. apply orb_prop in H as [H|H].
  - apply sv_eqb_eq in H. subst v. reflexivity.
  - destruct v as [|k o| | | | | | | | |]; try discriminate. destruct t as [|kt ot| | | | | | | | |]; try discriminate.
    pose proof (proj2 (syntactic_eq_sound E fs FH (VP kt wzero) (VP k (wsub o ot))) H) as Hf. cbn [den] in Hf.
    apply bv_eq. apply (f_equal bv_unsigned) in Hf. rewrite !bv_add_unsigned, !wbv_unsigned in Hf. rewrite wsub_ok, wzero_ok in Hf.
    unfold bv_wrap in Hf. rewrite bv_modulus_64 in Hf. rewrite Z.add_0_r in Hf.
    pose proof (bv_unsigned_in_range _ (ev E kt)) as RK. rewrite bv_modulus_64 in RK. rewrite (Z.mod_small _ _ RK) in Hf.
    cbn [den]. rewrite !bv_add_unsigned, !wbv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. rewrite Hf.
    rewrite Zplus_mod_idemp_l.
    replace (bv_unsigned (ev E k) + (w2Z o - w2Z ot) mod two64 + w2Z ot) with ((bv_unsigned (ev E k) + w2Z ot) + (w2Z o - w2Z ot) mod two64) by lia.
    rewrite Zplus_mod_idemp_r. f_equal. lia.
Qed.

Section WithPc.
Variable SHR_PC : int.
Variable isV : bool.

Definition KD : int := if isV then 3%uint63 else 2%uint63.

Definition gshr_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 then
        match List.find (fun w => match kind_of w with Some kd => kd =? to_Z KD | None => false end) ws, nth 0 ca (VL wzero) with
        | Some ((VP k o, _, _) as w16), VP kR oR =>
            match IMap.find k (s_regs st), IMap.find kR (s_regs st) with
            | Some r, Some rR =>
                if weqb o wzero && negb (PrimInt63.eqb k 0%uint63) && win3_eqb w16 (GRoom.top_win k 16%uint63 KD)
                   && negb (PrimInt63.eqb kR 0%uint63) && negb (PrimInt63.eqb kR k)
                   && GRoom.only_kind (to_Z KD) (Some (GRoom.top_win k 16%uint63 KD)) ws
                   && PrimInt63.eqb (rg_lo r) 0%uint63 && sv_eqb (rg_hi r) (VL (wlit 16%uint63)) && rg_w r
                   && match rg_bg r with BGNone => true | _ => false end
                   && GRoom.cells_in8 (shrink8 r) && Z.ltb (Z.of_nat (length ws)) 4096
                then
                  let ws' := List.map (fun w => if win3_eqb w (GRoom.top_win k 16%uint63 KD) then GRoom.top_win k 8%uint63 KD else w) ws in
                  let st1 := surg st [k] [(k, shrink8 r)] (mk_args 1%uint63 aw ws' ca) [] (s_next st) in
                  let f (v : sv) := if same_end (s_facts st) v (VP k (wlit 8%uint63)) then VP k (wlit 8%uint63) else v in
                  Some [setregs st1 (IMap.add kR (GW.subst_cells f rR) (s_regs st1))]
                else None
            | _, _ => None
            end
        | _, _ => None
        end
      else None
  | None => None
  end.

Definition gshr_contract : contract := Contract SHR_PC gshr_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma gshr_sound_main : forall E st ms model st',
  st_ok segs OPS E st ms model -> gshr_apply st = Some [st'] -> st_ok segs OPS E st' ms model.
Proof.
  intros E st ms model st' HS AP.
  unfold gshr_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct (List.find _ ws) as [[[lo16 len16] kd16]|] eqn:FW; [|discriminate].
  destruct lo16 as [|k o| | | | | | | | |]; try discriminate.
  destruct (nth 0 ca (VL wzero)) as [|kR oR| | | | | | | | |] eqn:EROOT; try discriminate.
  destruct (IMap.find k (s_regs st)) as [r|] eqn:FR; [|discriminate].
  destruct (IMap.find kR (s_regs st)) as [rR|] eqn:FRR; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection AP as <-.
  apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND CI8]. apply andb_prop in COND as [COND BG].
  apply andb_prop in COND as [COND W]. apply andb_prop in COND as [COND HI16]. apply andb_prop in COND as [COND LO].
  apply andb_prop in COND as [COND OK16]. apply andb_prop in COND as [COND KRK]. apply andb_prop in COND as [COND KR0].
  apply andb_prop in COND as [COND W16]. apply andb_prop in COND as [O0 K0].
  apply negb_true_iff in KRK. apply negb_true_iff in KR0.
  apply Z.ltb_lt in WLEN. apply Uint63.eqb_correct in LO. apply sv_eqb_eq in HI16. apply negb_true_iff in K0.
  apply win3_eqb_eq in W16. apply find_some in FW as [INW _]. rewrite W16 in INW. clear W16 O0 o len16 kd16.
  assert (BGN : rg_bg r = BGNone) by (destruct (rg_bg r); try discriminate; reflexivity).

  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (the_op_full st 1%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DEC.
  rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 1%uint63) with 1 in HC.

  set (w16 := GRoom.top_win k 16 KD) in *. set (w8 := GRoom.top_win k 8 KD) in *.
  assert (D16 : wden E w16 = Win (bv_unsigned (ev E k)) 16 (to_Z KD)) by (subst w16; rewrite GRoom.top_win_den; reflexivity).
  assert (D8 : wden E w8 = Win (bv_unsigned (ev E k)) 8 (to_Z KD)) by (subst w8; rewrite GRoom.top_win_den; reflexivity).
  assert (KDV : to_Z KD = 2 \/ to_Z KD = 3) by (unfold KD; destruct isV; [right| left]; reflexivity).
  pose proof (proj1 (Forall_forall _ _) WF (wden E w16) (in_map _ _ _ INW)) as WF16. rewrite D16 in WF16.
  destruct WF16 as (R0 & _ & R2 & [(KS & _)|[(KB & _)|(_ & blk & INB & SUBB)]]);
    [cbn [w_kind] in KS; unfold K_STACK in KS; lia| cbn [w_kind] in KB; unfold K_BLOCK in KB; lia|].
  cbn [w_lo w_len] in R0, R2.

  pose proof (Preg k r FR) as RO.
  assert (LOZ : loZ r = 0) by (unfold loZ; rewrite LO; reflexivity).
  assert (HIZ16 : hiZ E r = 16) by (unfold hiZ; rewrite HI16; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  assert (LOZ8 : loZ (shrink8 r) = 0) by (unfold loZ, shrink8; cbn [rg_lo]; rewrite LO; reflexivity).
  assert (HIZ8 : hiZ E (shrink8 r) = 8) by (unfold hiZ, shrink8; cbn [rg_hi den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  set (ws' := List.map (fun w => if win3_eqb w w16 then w8 else w) ws) in *.
  assert (LEN' : Z.of_nat (length ws') < two63) by (subst ws'; rewrite length_map; unfold two63; lia).
  assert (INWS' : forall w, In w ws' -> (In w ws /\ w <> w16) \/ w = w8).
  { intros w Hw. subst ws'. apply in_map_iff in Hw as (x & EQ & Hx). destruct (win3_eqb x w16) eqn:Q.
    - right. congruence.
    - left. subst w. split; [exact Hx|]. intros ->. rewrite win3_eqb_refl in Q. discriminate. }
  assert (INW8 : In w8 ws').
  { subst ws'. apply in_map_iff. exists w16. rewrite win3_eqb_refl. split; [reflexivity| exact INW]. }
  cbv zeta.
  match goal with |- st_ok _ _ _ (setregs ?S1 (IMap.add _ _ ?R)) _ _ => change R with (s_regs S1) end.
  apply (GW.st_ok_subst_cells segs OPS E _ ms model kR rR); [| | exact KR0|].
  2:{ cbn [surg s_regs]. assert (ND1 : List.NoDup (map fst [(k, shrink8 r)])) by (cbn [map fst]; constructor; [intros []| constructor]).
      apply (proj2 (find_add_regions _ _ kR rR (remove_keys_bst _ _ Pbst) ND1)).
      right. split; [cbn [map fst In]; intros [X|[]]; rewrite X, Uint63.eqb_refl in KRK; discriminate|].
      apply (proj2 (find_remove_keys _ _ kR rR Pbst)). split; [| exact FRR].
      cbn [In]. intros [X|[]]. rewrite X, Uint63.eqb_refl in KRK. discriminate. }
  2:{ intros v. destruct (same_end (s_facts st) v (VP k (wlit 8))) eqn:Q; [|reflexivity].
      symmetry. exact (same_end_sound E (s_facts st) v _ Pfacts Q). }
  apply (surgery_sound segs OPS E (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [k] [(k, shrink8 r)] (mk_args 1%uint63 aw ws' _) [] (s_next st)).
  - intros k' [<-|[]]. split; [exact K0|]. exists r. auto.
  - constructor; [intros []| constructor].
  - intros k' r' [H|[]]. injection H as <- <-. exact K0.
  -
    intros k' r' [H|[]]. injection H as <- <-.
    apply (region_ok_fresh segs (s_priv st) E (ms_mem ms) k (shrink8 r) K0).
    + cbn [shrink8 rg_cells]. apply IMap.bst_remove. exact (ro_bst _ _ _ _ _ _ RO).
    + cbn [shrink8 rg_bg]. exact BGN.
    + rewrite LOZ8. lia.
    + rewrite HIZ8. lia.
    + intros a Ha. rewrite LOZ8, HIZ8 in Ha.
      apply (aw_user_ok segs IMGX AW _ LB _ (ms_mem ms) model blk a HA INB). apply SUBB. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. lia.
    + intros gk gr F. cbn [shrink8 rg_cells] in F.
      assert (G1 : gk <> 1%uint63) by (intros ->; rewrite (IMap.find_remove_same _ _ (ro_bst _ _ _ _ _ _ RO)) in F; discriminate).
      pose proof F as F0. rewrite (IMap.find_remove_other _ _ _ (ro_bst _ _ _ _ _ _ RO) (fun X => G1 (eq_sym X))) in F0.
      split; [exact (ro_cells _ _ _ _ _ _ RO gk gr F0)|].
      intros c i Hc Hi.
      destruct (GRoom.cells_in8_sound (shrink8 r) gk gr c CI8 ltac:(cbn [shrink8 rg_cells]; apply IMap.bst_remove; exact (ro_bst _ _ _ _ _ _ RO)) F Hc) as [-> LE8].
      change (keyZ 0%uint63) with 0. rewrite LOZ8, HIZ8. pose proof (int_range (c_idx c)). lia.
  -
    intros k' r' a [H|[]] IR. injection H as <- <-. right. exists k, r. split; [left; reflexivity|]. split; [exact FR|].
    unfold inR in *. rewrite LOZ8, HIZ8 in IR. rewrite LOZ, HIZ16. lia.
  - intros k1 r1 k2 r2 a [H1|[]] [H2|[]] NE12. injection H1 as <- <-. injection H2 as <- <-. contradiction.
  -
    rewrite (ho_holds _ _ _ _ _ HOPS).
    cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC.
    destruct (decode_uc (map (den E) ca)) as [u|] eqn:DUC; [|contradiction].
    destruct HC as (g & L & P & O & Wk & M & CS0 & AX0 & SE).
    exists 1, (den E aw), (map (wden E) ws'), (map (den E) ca), LB.
    split; [apply mk_args_sound; exact LEN'|].

    split; [apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); apply (UOK.unp_wins_keep_map E 1 g LB ws ws' P O Wk);
            [intros x Hx; destruct (INWS' x Hx) as [[Hx0 _]| ->]; [left; exact Hx0| right; left; subst w8; apply UOK.kind_sub; unfold KD; destruct isV; vm_compute; reflexivity]
            |intros x Hx; destruct (UOK.map_replace_old ws w16 w8 x Hx) as [H0| ->];
             [left; exact H0| right; left; subst w16; apply UOK.kind_sub; unfold KD; destruct isV; vm_compute; reflexivity]]|]. split.
    + unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
      destruct (INWS' x Hx) as [[Hx0 _]| ->].
      * exact (proj1 (Forall_forall _ _) WF (wden E x) (in_map _ _ _ Hx0)).
      * rewrite D8. unfold window_wf. cbn [w_lo w_len w_kind w_iv].
        split; [lia|]. split; [lia|]. split; [lia|].
        right; right. split; [unfold K_SUB; lia|]. exists blk. split; [exact INB|].
        intros a Ha. apply SUBB. unfold in_iv, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. lia.
    + cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. rewrite DUC.
      assert (NP : forall w, In w (map (wden E) ws') -> pot_win w -> In w (map (wden E) ws)).
      { apply UOK.pot_map_old. intros x Hx. destruct (INWS' x Hx) as [[Hx0 _]| ->]; [left; exact Hx0| right]. rewrite D8. cbn [w_kind]. unfold K_STACK. lia. }
      exists g. split; [exact L| split; [exact P| split; [exact O| split; [| split; [exact M| split; [exact (cons_ok_ws _ _ _ _ _ _ CS0 NP)| split; [exact (acct_pot_ws _ _ _ _ _ AX0 NP)|]]]]]]];
        [|
           apply (SealX.seal_ok_map _ _ _ _ _ SE); intros x Hx; destruct (INWS' x Hx) as [[Hx0 _]| ->]; [left; exact Hx0| right];
           rewrite D8; cbn [w_kind]; unfold Seal.K_TWIN; lia].
      unfold wins_ok in *. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx).
      destruct (INWS' x Hx) as [[Hx0 _]| ->].
      * exact (proj1 (Forall_forall _ _) Wk (wden E x) (in_map _ _ _ Hx0) NS).
      * pose proof (proj1 (Forall_forall _ _) Wk (wden E w16) (in_map _ _ _ INW)) as W0. rewrite D16 in W0. rewrite D8 in *.
        destruct (W0 ltac:(cbn [w_kind]; unfold K_STACK; lia)) as [[KDJ DJ]|[NB SO]].
        -- left. split; [exact KDJ|]. intros b Hb a Ha. apply (DJ b Hb a). unfold in_iv, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. lia.
        -- right. split; [exact NB|]. unfold sub_ok in SO |- *. cbv zeta in SO |- *. cbn [w_kind w_lo w_len] in SO |- *.
           destruct SO as [(A1 & A2 & A3 & A4)|[(A1 & A2 & A3 & A4)|[(A1 & lD & A2 & A3 & A4)|(A1 & A2 & A3)]]].
           ++ left. repeat split; auto; lia.
           ++ right; left. repeat split; auto; lia.
           ++ right; right; left. split; [exact A1|]. exists lD. split; [exact A2|]. split; [exact A3| lia].
           ++ right; right; right. repeat split; auto; lia.
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 1 _ (map (wden E) ws') _ a (mk_args_sound E 1%uint63 aw ws' _ LEN'))) in FPa as (RA & NI & NW).
    split.
    + destruct (in_ws_dec (map (wden E) ws) a) as [IN|NIN].
      * right. exists k, r. split; [left; reflexivity|]. split; [exact FR|].
        apply in_ws_map_iff in IN as (x & Hx & Ha).
        destruct (win3_eqb x w16) eqn:Q.
        -- apply win3_eqb_eq in Q. subst x. rewrite D16 in Ha. unfold in_iv, w_iv in Ha. cbn [w_lo w_len fst snd] in Ha.
           unfold inR. rewrite LOZ, HIZ16. lia.
        -- exfalso. apply NW. apply in_ws_map_iff. exists x. split; [| exact Ha]. subst ws'. apply in_map_iff. exists x. rewrite Q. auto.
      * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E) ws) _ a DEC)). auto.
    + intros k' r' [H|[]] IR. injection H as <- <-. apply NW. apply in_ws_map_iff. exists w8. split; [exact INW8|].
      rewrite D8. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. unfold inR in IR. rewrite LOZ8, HIZ8 in IR. lia.
  - constructor.
Qed.

Theorem gshr_sound : contract_sound segs OPS MP PB gshr_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [gshr_contract c_apply] in HAP.
  destruct (gshr_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  2: { injection HAP as <-. apply (Hk st' (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP).
       exact (gshr_sound_main E st ms model st' HS AP). }
  all: exfalso; unfold gshr_apply in AP;
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End WithPc.
End GShr.
