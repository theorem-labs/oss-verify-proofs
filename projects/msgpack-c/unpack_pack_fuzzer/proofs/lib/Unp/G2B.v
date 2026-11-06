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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp G3 GWin G1.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GFast.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 GW.
Open Scope Z_scope.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module G2B.

Definition item_kind (t : Z) : option bool :=
  if (t =? T_STR) || (t =? T_BIN) then Some false else if t =? T_EXT then Some true else None.

Definition size_cell (isExt : bool) (nsv SZ : sv) : bool :=
  if isExt then same32 nsv (VAlu ALU_ADD SZ (VL wones)) || existsb (fun X => msame nsv (VAlu ALU_ADD X (VL wones))) [SZ; core32 SZ]
  else same32 nsv SZ || existsb (fun X => msame nsv X) [SZ; core32 SZ].

Definition range_nz (fs : list fact) (k : int) : bool :=
  match find_range fs k with Some (lo, hi) => negb (weqb lo wzero) | None => false end.

Definition g2b_hdr (R : IMap.t region) (ws : list (sv * sv * sv)) (D0 : bool) (root slot : sv) (kA kZ : int)
  : option (sv * sv * sv * int) :=
  if D0 then
    match root with
    | VP kR oR =>
        match okey oR, IMap.find kR R with
        | Some key, Some rR =>
            if negb (PrimInt63.eqb kR 0%uint63) && negb (PrimInt63.eqb kR kA) && negb (PrimInt63.eqb kR kZ)
               && only_kind 4 None ws && Z.ltb (keyZ key + 24) two62Z
            then match cell_at rR (keyZ key) 4%uint63, cell_at rR (keyZ key + 8) 4%uint63, cell_at rR (keyZ key + 16) 8%uint63 with
                 | Some a, Some b, Some c => Some (a, b, c, 0%uint63)
                 | _, _, _ => None
                 end
            else None
        | _, _ => None
        end
    | _ => None
    end
  else
    match slot with
    | VP kS os =>
        if weqb os wzero && negb (PrimInt63.eqb kS 0%uint63) && negb (PrimInt63.eqb kS kA) && negb (PrimInt63.eqb kS kZ)
           && only_kind 4 (Some (slot_win kS)) ws && existsb (win3_eqb (slot_win kS)) ws
        then match IMap.find kS R with
             | Some rS =>
                 if PrimInt63.eqb (rg_lo rS) 0%uint63 && sv_eqb (rg_hi rS) (VL (wlit 24%uint63)) && rg_w rS then
                 match cell_at rS 0 4%uint63, cell_at rS 8 4%uint63, cell_at rS 16 8%uint63 with
                 | Some a, Some b, Some c => Some (a, b, c, kS)
                 | _, _, _ => None
                 end
                 else None
             | None => None
             end
        else None
    | _ => None
    end.

Section WithPc.
Variable CONSUME_PC : int.

Definition g2b_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 then
      match ca with
      | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
          let fs := s_facts st in let n0 := s_next st in let R := s_regs st in
          let D0 := sv_eqb cb ce in
          match find_first is_carve ws, zh with
          | Some ((VP kA oA, SZ, _) as wA), VP kZ oz =>
              let wZ := top_win kZ 56%uint63 1%uint63 in
              if st_vars_below n0 st && PrimInt63.ltb 0%uint63 n0 && PrimInt63.ltb n0 (PrimInt63.sub bit62i 8%uint63)
                 && Z.ltb (Z.of_nat (length ws)) 4000
                 && weqb oA wzero && weqb oz wzero
                 && negb (PrimInt63.eqb kA 0%uint63) && negb (PrimInt63.eqb kZ 0%uint63) && negb (PrimInt63.eqb kA kZ)
                 && only_kind 5 (Some wA) ws && existsb (win3_eqb wZ) ws
                 && (if D0 then true else match decide_ltu_t fs cb ce with Some true => true | _ => false end)
                 && implied_t fs (FULe zptr (VP kA wzero))
                 && implied_t fs (FULe (VAlu ALU_ADD (VP kA wzero) SZ) (VAlu ALU_ADD zptr zfree))
                 && match decide_ltu_t fs SZ (VL (wlit 1001%uint63)) with Some true => true | _ => false end
                 && range_nz fs kA
              then
              match IMap.find kA R, IMap.find kZ R with
              | Some rA, Some rZ =>
                  if PrimInt63.eqb (rg_lo rA) 0%uint63 && sv_eqb (rg_hi rA) SZ && rg_w rA
                     && match rg_bg rA with BGNone => true | _ => false end
                     && PrimInt63.eqb (rg_lo rZ) 0%uint63 && sv_eqb (rg_hi rZ) (VL (wlit 56%uint63)) && rg_w rZ
                  then
                  match gran8 rZ 1%uint63, gran8 rZ 2%uint63, g2b_hdr R ws D0 root slot kA kZ with
                  | Some (d1, zfS), Some (d2, zpS), Some (tv, nsv, pv, kS) =>
                      match lit tv with
                      | Some ti =>
                          match item_kind (to_Z ti) with
                          | Some isExt =>
                              if sv_eqb pv (VP kA wzero) && size_cell isExt nsv SZ
                                 && (if isExt then match GFast.GFast.decide_eq0_tf fs SZ with Some false => true | _ => false end else true)
                                 && G1.g1_zone fs kA SZ zptr zfree zpS zfS
                              then
                                let nZP := n0 in let nZF := PrimInt63.add n0 1%uint63 in
                                let rZ' := set_cell8 (set_cell8 rZ 2%uint63 d2 (VP nZP wzero)) 1%uint63 d1 (VP nZF wzero) in
                                let KS := [kA; kZ] ++ (if D0 then [] else [kS]) in
                                let dead (w : sv * sv * sv) := win3_eqb w wA || (negb D0 && win3_eqb w (slot_win kS)) in
                                let ws' := List.filter (fun w => negb (dead w)) ws in
                                let ca' := [root; cb; ce; ccap; vb; ve; vcap; VP nZP wzero; VP nZF wzero; c0; slot; tD; restD;
                                            (if D0 then tv else rootT); (if D0 then sv_ext_c false 0%uint63 4%uint63 nsv else n1); (if D0 then VP kA wzero else P1); VP kZ oz] in

                                let nf := zp_facts fs kA nZP ++ zf_facts fs zfree nZF
                                          ++ [FULt SZ (VL (wlit 1001%uint63)); FULt (sv_ext_c false 0%uint63 4%uint63 nsv) (VL (wlit 1001%uint63))] in

                                match GPot.GPot.pot_scan_c fs aw ws with
                                | Some sc =>
                                    if GPot.GPot.pot_pre fs aw sc then
                                      let nP := PrimInt63.add n0 2%uint63 in
                                      Some [surg st KS [(kZ, rZ')] (mk_args 2%uint63 aw (GPot.GPot.pot_sym sc nP ws') ca')
                                                 (GPot.GPot.pot_facts_body sc nP SZ ++ nf) (GPot.GPot.pot_next sc (PrimInt63.add n0 2%uint63))]
                                    else None
                                | None => None
                                end
                              else None
                          | None => None
                          end
                      | None => None
                      end
                  | _, _, _ => None
                  end
                  else None
              | _, _ => None
              end
              else None
          | _, _ => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Definition g2b_contract : contract := Contract CONSUME_PC g2b_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Ltac is_arith T :=
  lazymatch T with
  | G1.hide _ => fail
  | (@eq Z _ _) => idtac | (not (@eq Z _ _)) => idtac
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | (_ /\ _) => idtac | (_ \/ _) => idtac
  | _ => fail
  end.
Ltac revert_arith :=
  repeat match goal with
         | H : ?T |- _ => tryif is_arith T then revert H else fail
         end.
Ltac alia := revert_arith; let K := fresh "aliaK" in pose proof I as K; clear - K; intros; lia.

Lemma item_kind_sound : forall t b, item_kind t = Some b ->
  (b = false /\ (t = T_STR \/ t = T_BIN)) \/ (b = true /\ t = T_EXT).
Proof.
  intros t b H. unfold item_kind in H.
  destruct ((t =? T_STR) || (t =? T_BIN)) eqn:C.
  - injection H as <-. left. split; [reflexivity|]. apply orb_prop in C as [C|C]; apply Z.eqb_eq in C; [left|right]; exact C.
  - destruct (t =? T_EXT) eqn:C2; [|discriminate]. injection H as <-. right. split; [reflexivity|]. apply Z.eqb_eq in C2. exact C2.
Qed.

Lemma size_cell_sound : forall E isExt nsv SZ, size_cell isExt nsv SZ = true ->
  let s := bv_unsigned (den E SZ) in
  s < 2 ^ 32 -> (isExt = true -> 1 <= s) ->
  bv_unsigned (den E nsv) mod 2 ^ 32 = (if isExt then s - 1 else s).
Proof.
  intros E isExt nsv SZ H s SB EX. unfold size_cell in H.
  pose proof (bv_unsigned_in_range _ (den E SZ)) as RS. rewrite bv_modulus_64 in RS. fold s in RS.
  pose proof (bv_unsigned_in_range _ (den E nsv)) as RN. rewrite bv_modulus_64 in RN.
  assert (CX : forall X, In X [SZ; core32 SZ] -> bv_unsigned (den E X) mod 2 ^ 32 = s).
  { intros X [<-|[<-|[]]]; [apply Z.mod_small; subst s; lia|]. rewrite core32_den. apply Z.mod_small. subst s; lia. }
  destruct isExt.
  - specialize (EX eq_refl). apply orb_prop in H as [H|H].
    { rewrite (same32_sound E _ _ H). change (den E (VAlu ALU_ADD SZ (VL wones))) with (alu64 ALU_ADD (den E SZ) (den E (VL wones))).
      cbn [alu64 alu den]. rewrite bv_add_unsigned, wbv_unsigned. change (w2Z wones) with (two64 - 1). unfold bv_wrap. rewrite bv_modulus_64.
      fold s. replace (s + (two64 - 1)) with ((s - 1) + 1 * two64) by (clear; lia). rewrite Z_mod_plus_full.
      rewrite (Z.mod_small (s - 1) two64) by (clear - EX SB; unfold two64; lia). apply Z.mod_small. clear - EX SB. lia. }
    apply existsb_exists in H as (X & HX & Q). pose proof (msame_sound E _ _ Q) as M.
    apply (f_equal bv_unsigned) in M. cbn [den alu64 alu] in M. rewrite bv_add_unsigned, wbv_unsigned in M. change (w2Z wones) with (two64 - 1) in M.
    unfold bv_wrap in M. rewrite bv_modulus_64 in M. rewrite M.
    pose proof (CX X HX) as MX. pose proof (bv_unsigned_in_range _ (den E X)) as RX. rewrite bv_modulus_64 in RX.
    set (x := bv_unsigned (den E X)) in *.
    pose proof (Z.div_mod x (2 ^ 32) ltac:(clear; lia)) as XE. rewrite MX in XE. set (q := x / 2 ^ 32) in *.
    assert (Q0 : 0 <= q) by (subst q; apply Z.div_pos; clear - RX; lia).
    replace (x + (two64 - 1)) with ((x - 1) + 1 * two64) by (clear; lia).
    rewrite Z_mod_plus_full. rewrite (Z.mod_small (x - 1) two64) by (clear - XE Q0 EX RX; unfold two64 in *; lia).
    rewrite XE. replace (2 ^ 32 * q + s - 1) with ((s - 1) + q * 2 ^ 32) by (clear; lia).
    rewrite Z_mod_plus_full. apply Z.mod_small. clear - EX SB. lia.
  - apply orb_prop in H as [H|H].
    + rewrite (same32_sound E nsv SZ H). apply Z.mod_small. subst s; lia.
    + apply existsb_exists in H as (X & HX & Q). pose proof (msame_sound E _ _ Q) as M. rewrite M. exact (CX X HX).
Qed.

Lemma range_nz_sound : forall E fs k, facts_hold E fs -> range_nz fs k = true -> bv_unsigned (ev E k) <> 0.
Proof.
  intros E fs k FH H. unfold range_nz in H. destruct (find_range fs k) as [[lo hi]|] eqn:FR; [|discriminate].
  apply negb_true_iff in H. pose proof (find_range_sound_gen E fs FH k lo hi FR) as [L _].
  assert (w2Z lo <> 0).
  { intros X. assert (lo = wzero) by (apply w2Z_inj; rewrite X, wzero_ok; reflexivity). subst lo. rewrite weqb_refl in H. discriminate H. }
  pose proof (w2Z_range lo). lia.
Qed.

Lemma neqb_neq : forall a b, negb (PrimInt63.eqb a b) = true -> a <> b.
Proof. intros a b H. apply negb_true_iff in H. exact (Uint63.eqb_false_correct _ _ H). Qed.
Lemma neq_eqb : forall a b, a <> b -> PrimInt63.eqb a b = false.
Proof. intros a b H. apply (proj2 (Uint63.eqb_false_spec _ _)). exact H. Qed.

Lemma g2b_sound_main : forall E st ms model st',
  st_ok segs OPS E st ms model -> g2b_apply st = Some [st'] ->
  exists E', env_ext (s_next st) E E' /\ st_ok segs OPS E' st' ms model.
Proof.
  intros E st ms model st' HS0 AP. unfold g2b_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbv zeta in AP.
  destruct (find_first is_carve ws) as [[[a1 SZ] a3]|] eqn:FCV; [|discriminate].
  destruct a1 as [|kA oA| | | | | | | | |]; try discriminate.
  destruct zh as [|kZ oz| | | | | | | | |]; try discriminate.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  destruct (IMap.find kA (s_regs st)) as [rA|] eqn:FA; [|discriminate].
  destruct (IMap.find kZ (s_regs st)) as [rZ|] eqn:FZ; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND2; [|discriminate] end.
  destruct (gran8 rZ 1) as [[d1 zfS]|] eqn:GZF; [|discriminate].
  destruct (gran8 rZ 2) as [[d2 zpS]|] eqn:GZP; [|discriminate].
  destruct (g2b_hdr (s_regs st) ws (sv_eqb cb ce) root slot kA kZ) as [[[[tv nsv] pv] kS]|] eqn:HDR; [|discriminate].
  destruct (lit tv) as [ti|] eqn:LT; [|discriminate].
  destruct (item_kind (to_Z ti)) as [isExt|] eqn:IK; [|discriminate].
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND3; [|discriminate] end.
  destruct (GPot.GPot.pot_scan_c (s_facts st) aw ws) as [sc|] eqn:SCAN; [|discriminate].
  destruct (GPot.GPot.pot_pre (s_facts st) aw sc) eqn:PRE; [|discriminate].
  injection AP as <-.
  set (n0 := s_next st) in *. set (D0b := sv_eqb cb ce) in *. set (fs := s_facts st) in *.
  set (t := to_Z ti) in *.

  apply andb_prop in COND as [COND RNZ]. apply andb_prop in COND as [COND LIMB]. apply andb_prop in COND as [COND IMP2]. apply andb_prop in COND as [COND IMP1].
  apply andb_prop in COND as [COND DDEC]. apply andb_prop in COND as [COND EXZ]. apply andb_prop in COND as [COND OK5].
  apply andb_prop in COND as [COND NAZ]. apply andb_prop in COND as [COND KZ0]. apply andb_prop in COND as [COND KA0'].
  apply andb_prop in COND as [COND OZ]. apply andb_prop in COND as [COND OA]. apply andb_prop in COND as [COND WLEN].
  apply andb_prop in COND as [COND N62]. apply andb_prop in COND as [VB NPOS].
  apply neqb_neq in NAZ. apply negb_true_iff in KZ0. apply negb_true_iff in KA0'.
  apply (proj1 (weqb_ok _ _)) in OZ. subst oz. apply (proj1 (weqb_ok _ _)) in OA. subst oA.
  apply Z.ltb_lt in WLEN. apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS.
  apply Uint63.ltb_spec in N62. replace (to_Z (PrimInt63.sub bit62i 8%uint63)) with (to_Z bit62i - 8) in N62 by (vm_compute; reflexivity).
  apply G1.existsb_win_In in EXZ.
  apply andb_prop in COND2 as [COND2 WZ]. apply andb_prop in COND2 as [COND2 HIZ56]. apply andb_prop in COND2 as [COND2 LOZ].
  apply andb_prop in COND2 as [COND2 BGA]. apply andb_prop in COND2 as [COND2 WA]. apply andb_prop in COND2 as [LOA HIA].
  apply sv_eqb_eq in HIZ56. apply Uint63.eqb_correct in LOZ. apply Uint63.eqb_correct in LOA. apply sv_eqb_eq in HIA.
  apply andb_prop in COND3 as [COND3 ZONE]. apply andb_prop in COND3 as [COND3 EX1]. apply andb_prop in COND3 as [PV SZC].
  apply sv_eqb_eq in PV. subst pv.

  destruct (find_first_some _ is_carve ws _ FCV) as [INA ISC]. unfold is_carve in ISC.
  destruct a3 as [k5| | | | | | | | | |]; try discriminate.
  apply andb_prop in ISC as [ISC K5]. apply andb_prop in ISC as [ISC NT5]. apply andb_prop in ISC as [_ KA0].
  apply negb_true_iff in KA0. apply negb_true_iff in NT5. apply Uint63.eqb_correct in K5.
  assert (K5E : k5 = wlit 5%uint63) by (destruct k5 as [kt kl]; cbn [wt wl] in NT5, K5; subst; reflexivity). subst k5.

  assert (TZ1 : to_Z (PrimInt63.add n0 1) = to_Z n0 + 1) by (rewrite to_Z_add_small; [reflexivity| alia| change (to_Z 1%uint63) with 1; alia]).
  assert (TZ2 : to_Z (PrimInt63.add n0 2) = to_Z n0 + 2) by (rewrite to_Z_add_small; [reflexivity| alia| change (to_Z 2%uint63) with 2; alia]).
  set (nZF := PrimInt63.add n0 1) in *. set (nP := PrimInt63.add n0 2) in *.

  pose proof HS0 as [_ _ _ _ _ _ _ _ _ Pbst0 Preg0 _ _ _ _ _ _ _].
  destruct (the_op_full st 1%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n0 st o VB (op_in_In st o OPS1)) as VBo.
  assert (INCA : forall v, In v [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; VP kZ wzero] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (INW : forall w, In w ws -> In (fst (fst w)) (op_args o) /\ In (snd (fst w)) (op_args o) /\ In (snd w) (op_args o)).
  { intros [[w1 w2] w3] Hw. destruct (in_flat_windows ws w1 w2 w3 Hw) as (I1 & I2 & I3). rewrite ARGS. cbn [fst snd].
    repeat split; right; right; right; apply in_app_iff; left; assumption. }
  assert (LTn : forall k o', In (VP k o') (op_args o) -> to_Z k < to_Z n0).
  { intros k o' Hk. pose proof (VBo _ Hk) as X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
  assert (KA_LT : to_Z kA < to_Z n0) by exact (LTn kA wzero (proj1 (INW _ INA))).
  assert (KZ_LT : to_Z kZ < to_Z n0) by exact (LTn kZ wzero (INCA _ ltac:(do 16 right; left; reflexivity))).
  assert (VBSZ : sv_vars_below n0 SZ = true) by exact (VBo _ (proj1 (proj2 (INW _ INA)))).
  pose proof (ro_bst _ _ _ _ _ _ (Preg0 kZ rZ FZ)) as BRZ.
  assert (VBzpS : sv_vars_below n0 zpS = true) by exact (gran8_vars_below n0 st kZ rZ 2%uint63 d2 zpS VB Pbst0 BRZ FZ GZP).
  assert (VBzfS : sv_vars_below n0 zfS = true) by exact (gran8_vars_below n0 st kZ rZ 1%uint63 d1 zfS VB Pbst0 BRZ FZ GZF).

  set (wZP := den E zpS). set (wZF := den E zfS).
  set (wP := Z_to_bv 64 (GPot.GPot.pot_word E sc + (40 + 4 * bv_unsigned (den E SZ)))).
  set (E' := env_upd (env_upd (env_upd E n0 wZP) nZF wZF) nP wP).
  assert (HX : env_ext n0 E E').
  { subst E'. eapply (env_ext_trans n0 nP); [alia| | apply env_upd_ext]. eapply (env_ext_trans n0 nZF); [alia| | apply env_upd_ext]. apply env_upd_ext. }
  assert (EZP : ev E' n0 = wZP).
  { subst E'. rewrite (ev_upd_other _ nP) by alia. rewrite (ev_upd_other _ nZF) by alia. apply env_upd_same. }
  assert (EZF : ev E' nZF = wZF) by (subst E'; rewrite (ev_upd_other _ nP) by alia; apply env_upd_same).
  assert (EP : ev E' nP = wP) by (subst E'; apply env_upd_same).
  assert (DR : forall v, In v (op_args o) -> den E' v = den E v) by (intros v Hv; exact (den_reval n0 E E' HX v (VBo v Hv))).
  assert (DzpS : den E' zpS = wZP) by exact (den_reval n0 E E' HX zpS VBzpS).
  assert (DzfS : den E' zfS = wZF) by exact (den_reval n0 E E' HX zfS VBzfS).
  clearbody E'.
  exists E'. split; [exact HX|].
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n0 E E' HX st ms model NPOS VB HS0).
  clear HS0 Pbst0 Preg0 BRZ.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].

  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E') as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 1%uint63) with 1 in HC.
  cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC. cbn [map decode_uc] in HC.
  destruct HC as (g & L & P & O & Wk & M & CS0 & [AX PTU] & SE). clear CS0.
  pose proof (GPot.GPot.pot_scan_c_ok E' (s_facts st) aw ws sc Pfacts SCAN) as SCOK.
  destruct (PTU eq_refl) as (S0 & KP0 & PA0). clear PTU.
  pose proof L as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
  cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap, Lzp, Lzf, Lc0, LD.
  pose proof (pf g P) as (VC & EC & SC & VV & EV8 & SV' & LV & LA & ZV).
  pose proof ZV as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7).
  pose proof P as (_ & _ & _ & CC & _ & _ & _ & CV & _ & DLIM & _ & _).
  destruct (head_chunk g P) as (h & hr & EH & HH1 & HH2 & HH3).
  assert (Hh : In h (z_chunks (u_zone g))) by (rewrite EH; left; reflexivity).
  pose proof (owned_chunk g h Hh) as OWNh.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block h) HA (proj1 O _ OWNh)) as (Bh1 & Bh2 & Bh3 & Bh4 & _).
  pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold two62Z in CEIL.
  unfold chunk_block in Bh1, Bh2, Bh3. cbn [fst snd] in Bh1, Bh2, Bh3. unfold CHUNK_HDR in Bh2, Bh3.
  assert (DLEN : u_D g = Z.of_nat (length (u_levels g))) by reflexivity.

  pose proof (Preg kA rA FA) as ROA. pose proof (Preg kZ rZ FZ) as ROZ.

  set (P_ := bv_unsigned (ev E' kA)) in *. set (ZB := bv_unsigned (ev E' kZ)) in *.
  set (bm := bmem_of segs (ms_mem ms)) in *.
  set (zp := z_ptr (u_zone g)) in *. set (zf := z_free (u_zone g)) in *. set (ls := u_levels g) in *.
  set (SZd := bv_unsigned (den E' SZ)) in *.
  assert (HIA' : hiZ E' rA = SZd) by (unfold hiZ; rewrite HIA; reflexivity).
  assert (LOA' : loZ rA = 0) by (unfold loZ; rewrite LOA; reflexivity).
  assert (LOZ' : loZ rZ = 0) by (unfold loZ; rewrite LOZ; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ ROA KA0) as RA. rewrite LOA', HIA' in RA. fold P_ in RA.
  pose proof (ro_range _ _ _ _ _ _ ROZ KZ0) as RZr. rewrite LOZ' in RZr. fold ZB in RZr.

  destruct (gran8_u64 segs _ E' (ms_mem ms) kZ rZ 1%uint63 d1 zfS ROZ KZ0 GZF ltac:(change (keyZ 1%uint63) with 1; alia) ltac:(change (keyZ 1%uint63) with 1; unfold two62Z; alia)) as (AZF & _ & HZ1).
  destruct (gran8_u64 segs _ E' (ms_mem ms) kZ rZ 2%uint63 d2 zpS ROZ KZ0 GZP ltac:(change (keyZ 2%uint63) with 2; alia) ltac:(change (keyZ 2%uint63) with 2; unfold two62Z; alia)) as (AZP & _ & HZ2).
  change (keyZ 1%uint63) with 1 in AZF, HZ1. change (keyZ 2%uint63) with 2 in AZP, HZ2. fold ZB bm in AZF, AZP. rewrite DzpS in AZP. rewrite DzfS in AZF.

  pose proof (G1.lit_val E' tv ti LT) as TSV. fold t in TSV.
  destruct (decide_ltu_t fs SZ (VL (wlit 1001))) as [[|]|] eqn:DLIM'; try discriminate.
  pose proof (decide_ltu_t_sound E' fs Pfacts _ _ _ DLIM') as LIM. apply (proj1 (ltu_iff _ _ true)) in LIM.
  replace (bv_unsigned (den E' (VL (wlit 1001)))) with 1001 in LIM by (cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity). fold SZd in LIM.
  pose proof (bv_unsigned_in_range _ (den E' SZ)) as RSZ. rewrite bv_modulus_64 in RSZ. fold SZd in RSZ.
  assert (EXT1 : isExt = true -> 1 <= SZd).
  { intros HE. rewrite HE in EX1. destruct (GFast.GFast.decide_eq0_tf fs SZ) as [[|]|] eqn:D0Q; try discriminate.
    pose proof (GFast.GFast.decide_eq0_tf_sound E' fs Pfacts SZ false D0Q) as NZ. apply (proj1 (eqb_iff _ _ false)) in NZ.
    assert (SZd <> 0) by (intros X; apply NZ; apply bv_eq; subst SZd; rewrite X, Z_to_bv_unsigned; reflexivity). alia. }
  pose proof (item_kind_sound t isExt IK) as IKS.
  set (nst := if isExt then SZd - 1 else SZd).
  assert (NSV : bv_unsigned (den E' nsv) mod 2 ^ 32 = nst).
  { subst nst. apply (size_cell_sound E' isExt nsv SZ SZC); [alia| exact EXT1]. }
  assert (T10 : 0 <= t <= 10) by (destruct IKS as [[_ [X|X]]|[_ X]]; rewrite X; unfold T_STR, T_BIN, T_EXT; alia).
  assert (TSV32 : bv_unsigned (den E' tv) mod 2 ^ 32 = t) by (rewrite TSV; apply Z.mod_small; alia).

  assert (CEND : v_end (u_cstk g) = v_begin (u_cstk g) + 8 * u_D g) by (unfold v_end; rewrite EC, SC; alia).
  assert (DZ : D0b = true -> ls = []).
  { intros HD. subst D0b. apply sv_eqb_eq in HD.
    assert (X : v_begin (u_cstk g) = v_end (u_cstk g)) by (rewrite Lcb, Lce, HD; reflexivity).
    rewrite CEND in X. subst ls. destruct (u_levels g); [reflexivity|]. exfalso. rewrite DLEN in X. cbn [length] in X. alia. }
  assert (DNZ : D0b = false -> ls <> []).
  { intros HD NIL. rewrite HD in DDEC. destruct (decide_ltu_t fs cb ce) as [[|]|] eqn:DL; try discriminate.
    pose proof (decide_ltu_t_sound E' fs Pfacts _ _ _ DL) as LTU. apply (proj1 (ltu_iff _ _ true)) in LTU.
    rewrite <- Lcb, <- Lce, CEND, DLEN in LTU. subst ls. rewrite NIL in LTU. cbn [length] in LTU. alia. }

  assert (CURSLOT : ls <> [] -> u_cur_slot g = bv_unsigned (den E' slot)).
  { intros NN. exact (proj1 (LD NN)). }
  assert (HDRS : (D0b = false -> u32_at bm (u_cur_slot g) t /\ u32_at bm (u_cur_slot g + 8) nst /\ u64_at bm (u_cur_slot g + 16) P_) /\
                 (D0b = true -> only_kind 4 None ws = true) /\
                 (D0b = false -> exists rS, slot = VP kS wzero /\ IMap.find kS (s_regs st) = Some rS /\ rg_lo rS = 0%uint63 /\ rg_hi rS = VL (wlit 24%uint63)
                                   /\ rg_w rS = true /\ In (slot_win kS) ws /\ only_kind 4 (Some (slot_win kS)) ws = true
                                   /\ kS <> 0%uint63 /\ kS <> kA /\ kS <> kZ)).
  { unfold g2b_hdr in HDR. destruct D0b.
    - destruct root as [|k1 oR| | | | | | | | |]; try discriminate.
      destruct (okey oR) as [key|] eqn:OK; [|discriminate]. destruct (IMap.find k1 (s_regs st)) as [r1|] eqn:F1; [|discriminate].
      match type of HDR with (if ?c then _ else _) = _ => destruct c eqn:CR; [|discriminate] end.
      destruct (cell_at r1 (keyZ key) 4) as [a|] eqn:C1; [|discriminate]. destruct (cell_at r1 (keyZ key + 8) 4) as [b|] eqn:C2; [|discriminate].
      destruct (cell_at r1 (keyZ key + 16) 8) as [c|] eqn:C3; [|discriminate]. injection HDR as E1 E2 E3 E4.
      apply andb_prop in CR as [CR _]. apply andb_prop in CR as [CR OK4].
      split; [intros X; discriminate X|]. split; [intros _; exact OK4| intros X; discriminate X].
    - destruct slot as [|kS0 os| | | | | | | | |]; try discriminate.
      match type of HDR with (if ?c then _ else _) = _ => destruct c eqn:CR; [|discriminate] end.
      destruct (IMap.find kS0 (s_regs st)) as [rS|] eqn:FS; [|discriminate].
      match type of HDR with (if ?c then _ else _) = _ => destruct c eqn:CR2; [|discriminate] end.
      destruct (cell_at rS 0 4) as [a|] eqn:C1; [|discriminate]. destruct (cell_at rS 8 4) as [b|] eqn:C2; [|discriminate].
      destruct (cell_at rS 16 8) as [c|] eqn:C3; [|discriminate]. injection HDR as E1 E2 E3 E4. subst a b c. subst kS0.
      apply andb_prop in CR as [CR EXS]. apply andb_prop in CR as [CR OK4]. apply andb_prop in CR as [CR NSZ]. apply andb_prop in CR as [CR NSA].
      apply andb_prop in CR as [OS KS0'].
      apply (proj1 (weqb_ok _ _)) in OS. subst os. apply negb_true_iff in KS0'.
      apply neqb_neq in NSZ. apply neqb_neq in NSA. apply G1.existsb_win_In in EXS.
      apply andb_prop in CR2 as [CR2 WS]. apply andb_prop in CR2 as [LOS HIS]. apply Uint63.eqb_correct in LOS. apply sv_eqb_eq in HIS.
      pose proof (Preg kS rS FS) as ROS.
      split; [| split; [intros X; discriminate X| intros _; exists rS; repeat split; auto; exact (Uint63.eqb_false_correct _ _ KS0')]].
      intros _. rewrite (CURSLOT (DNZ eq_refl)). rewrite (den_VP0 E' kS wzero (weqb_refl _)).
      destruct (cell_at_u32 segs _ E' (ms_mem ms) kS rS 0 tv ROS KS0' ltac:(alia) ltac:(unfold two62Z; alia) C1) as (X1 & _ & _).
      destruct (cell_at_u32 segs _ E' (ms_mem ms) kS rS 8 nsv ROS KS0' ltac:(alia) ltac:(unfold two62Z; alia) C2) as (X2 & _ & _).
      destruct (cell_at_u64 segs _ E' (ms_mem ms) kS rS 16 _ ROS KS0' ltac:(alia) ltac:(unfold two62Z; alia) C3) as (X3 & _ & _).
      fold bm in X1, X2, X3. rewrite Z.add_0_r in X1. rewrite TSV32 in X1. rewrite NSV in X2. rewrite (den_VP0 E' kA wzero (weqb_refl _)) in X3. fold P_ in X3.
      split; [exact X1|]. split; [exact X2| exact X3]. }
  destruct HDRS as (HD1c & HD0 & HD1).

  assert (ZPV : bv_unsigned (den E' zptr) = zp) by (symmetry; exact Lzp).
  assert (ZFV : bv_unsigned (den E' zfree) = zf) by (symmetry; exact Lzf).
  assert (CHI : chunk_hi h = zp + zf) by (subst zp zf; alia).
  assert (B1' : 0 <= P_ + SZd < two64) by (clear - RA RSZ; lia).
  assert (B2' : 0 <= zp + zf < two64) by (clear - Bh1 Bh2 Bh3 Bh4 CHI; rewrite <- CHI; unfold chunk_hi, CHUNK_HDR in *; lia).
  assert (ZLE : zp <= P_).
  { pose proof (implied_t_sound E' fs _ Pz Pfacts IMP1) as IF1. cbn [fact_holds] in IF1. rewrite ZPV, (den_VP0 E' kA wzero (weqb_refl _)) in IF1. exact IF1. }
  assert (ZHI : P_ + SZd <= zp + zf).
  { pose proof (implied_t_sound E' fs _ Pz Pfacts IMP2) as IF2. cbn [fact_holds] in IF2. rewrite !G1.den_VAlu in IF2. cbn [alu64 alu] in IF2.
    rewrite !bv_add_unsigned, (den_VP0 E' kA wzero (weqb_refl _)), ZPV, ZFV, !wrap64 in IF2. fold SZd in IF2. fold P_ in IF2.
    rewrite (Z.mod_small _ _ B1'), (Z.mod_small _ _ B2') in IF2. exact IF2. }
  set (zp' := bv_unsigned (den E' zpS)) in *. set (zf' := bv_unsigned (den E' zfS)) in *.
  assert (ZPS : zp' = P_ + SZd /\ zp' + zf' = zp + zf).
  { unfold G1.g1_zone in ZONE. apply existsb_exists in ZONE as (X & HX0 & Q). apply andb_prop in Q as [Q1 Q2].
    pose proof (anchor_defs_sound E' fs kA X Pfacts HX0) as DX.
    pose proof (msame_sound E' _ _ Q1) as M1. pose proof (msame_sound E' _ _ Q2) as M2.
    assert (M1' : zp' = (P_ + SZd) mod two64).
    { subst zp'. rewrite M1, G1.den_VAlu. cbn [alu64 alu]. rewrite bv_add_unsigned, DX, (den_VP0 E' kA wzero (weqb_refl _)), wrap64. reflexivity. }
    rewrite Z.mod_small in M1' by exact B1'.
    assert (M2' : (zp' + zf') mod two64 = zp + zf).
    { apply (f_equal bv_unsigned) in M2. rewrite !G1.den_VAlu in M2. cbn [alu64 alu] in M2. rewrite !bv_add_unsigned, !wrap64 in M2. fold zp' zf' in M2.
      replace (bv_unsigned (den E' (if sv_eqb zptr (VP kA wzero) then X else zptr))) with zp in M2.
      2:{ destruct (sv_eqb zptr (VP kA wzero)) eqn:QZ; [| symmetry; exact ZPV]. apply sv_eqb_eq in QZ. rewrite DX, <- QZ. symmetry. exact ZPV. }
      rewrite ZFV in M2. rewrite M2. apply Z.mod_small. exact B2'. }
    pose proof (bv_unsigned_in_range _ (den E' zfS)) as RF. rewrite bv_modulus_64 in RF. fold zf' in RF.
    pose proof (bv_unsigned_in_range _ (den E' zpS)) as RP. rewrite bv_modulus_64 in RP. fold zp' in RP.
    split; [exact M1'|].
    destruct (mod_ex (zp' + zf')) as [q Hq]. rewrite Hq in M2'. unfold two64 in *. alia. }
  destruct ZPS as [ZP1 ZP2].
  pose proof (bv_unsigned_in_range _ (den E' zfS)) as RF. rewrite bv_modulus_64 in RF. fold zf' in RF.

  set (z' := zone_bump (u_zone g) (zp' - zp)).
  set (g' := mkUnp (u_ctx g) (u_vis g) (u_data g) (u_len g) ls (u_cstk g) (u_vstk g) z').
  assert (ZG : zone_grows (u_zone g) z') by (apply zone_grows_bump; alia).
  assert (ZV' : zone_valid z').
  { subst z'. unfold zone_bump, zone_valid. cbn [z_chunks z_addr z_ptr z_free]. fold zp zf.
    split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. rewrite EH in *. cbn [hd] in *. unfold chunk_lo, chunk_hi, CHUNK_HDR in *.
    split; [alia|]. split; [alia|]. split; [alia|]. exact Z7. }
  assert (ZC' : z_chunks z' = z_chunks (u_zone g) /\ z_ptr z' = zp' /\ z_free z' = zf' /\ z_addr z' = z_addr (u_zone g) /\ z_head z' = z_head (u_zone g)).
  { subst z'. unfold zone_bump. cbn. fold zp zf. repeat split; alia. }
  destruct ZC' as (ZCc & ZCp & ZCf & ZCa & ZCh).
  assert (HH1' : fst h + 8 <= zp) by (unfold chunk_lo, CHUNK_HDR in HH1; exact HH1).
  assert (P0 : P_ <> 0) by exact (range_nz_sound E' fs kA Pfacts RNZ).
  assert (OWN' : owned g' = owned g) by (subst g'; unfold owned, cstk_block, vstk_block; cbn [u_cstk u_vstk u_zone]; rewrite ZCc; reflexivity).
  assert (PURE' : pure_ok g').
  { subst g'. unfold pure_ok. cbn [u_cstk u_vstk u_levels u_zone]. unfold u_D. cbn [u_levels]. fold ls. rewrite <- DLEN.
    split; [exact VC|]. split; [exact EC|]. split; [exact SC|]. split; [exact CC|].
    split; [exact VV|]. split; [exact EV8|]. split; [exact SV'|]. split; [exact CV|].
    split; [exact LV|]. split; [exact DLIM|]. split; [exact (levels_alloc_mono_zone _ _ _ ZG LA)| exact ZV']. }
  assert (OWNOK' : own_ok g' LB) by (unfold own_ok; rewrite OWN'; exact O).

  assert (INALLOC : in_alloc z' P_ SZd).
  { unfold in_alloc. right. rewrite ZCc, ZCp, EH. cbn [hd]. split; [clear - HH1 ZLE; lia| clear - ZP1; lia]. }
  assert (INZONE : in_zone z' P_ SZd) by (apply body_in_zone; [exact ZV'| exact INALLOC]).
  assert (RDISJ : forall l, In l ls -> rdisj P_ SZd (lv_slot l) (lv_unfilled l)).
  { intros l Hl. pose proof (proj1 (Forall_forall _ _) LV l Hl) as LVl. pose proof (LA) as [LA1 _]. pose proof (LA1 l Hl) as AL.
    destruct LVl as (A1 & A2 & A3 & A4 & A5).
    assert (PER : 1 <= per (lv_t l) <= 2) by (clear; destruct (lv_t l); cbn; lia).
    assert (KB : 0 <= lv_k l <= per (lv_t l) * lv_n l) by (unfold lv_k; clear - A1 A2; destruct (lv_t l); cbn; lia).
    assert (BY0 : 0 <= lv_bytes l) by (unfold lv_bytes, OBJ_SIZE; clear - A1 A2 PER; nia).
    pose proof (in_alloc_fresh_disj (u_zone g) (lv_P l) (lv_bytes l) P_ SZd ZV BY0 AL) as DJ.
    assert (SUBR : lv_P l <= lv_slot l /\ lv_slot l + lv_unfilled l <= lv_P l + lv_bytes l).
    { unfold lv_unfilled, lv_slot, lv_bytes, OBJ_SIZE. clear - KB PER. nia. }
    unfold rdisj in DJ |- *. fold zp in DJ. rewrite EH in DJ. cbn [hd] in DJ. rewrite CHI in DJ.
    specialize (DJ ltac:(clear - ZLE; lia) ltac:(clear - ZHI; lia)). clear - DJ SUBR. lia. }

  assert (RDB : readable bm P_ (Z.to_nat SZd)).
  { subst bm. apply (readable_of_region segs _ E' (ms_mem ms) kA rA P_ (Z.to_nat SZd) ROA KA0); rewrite ?LOA', ?HIA'; fold P_; [alia|]. rewrite Z2Nat.id by alia. alia. }

  set (ob := if isExt then OExt P_ (SZd - 1) else if t =? T_STR then OStr P_ SZd else OBin P_ SZd).
  assert (OBT : obj_type ob = t /\ obj_cnt ob = nst /\ obj_ptr ob = P_ /\ obj_bodies ob = [(P_, SZd)] /\ kids_at bm ob /\
                (forall a, tl (obj_cells a ob) = []) /\
                (forall a, hdr_at bm a ob <-> (u32_at bm a t /\ u32_at bm (a + 8) nst /\ u64_at bm (a + 16) P_)) /\
                tree_wf bm z' ob).
  { subst ob nst. destruct IKS as [[-> [TT|TT]]|[-> TT]]; rewrite TT.
    - change (T_STR =? T_STR) with true. cbn [obj_type obj_cnt obj_ptr obj_bodies kids_at obj_cells tl hdr_at tree_wf].
      replace (P_ =? 0) with false by (symmetry; apply Z.eqb_neq; exact P0).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|].
      split; [intros; reflexivity|]. split; [intros a; unfold hdr_at; cbn [obj_type]; tauto|].
      split; [unfold LIMIT; alia|]. split; [intros X; exfalso; exact (P0 X)|]. intros _. split; [exact INZONE| exact RDB].
    - change (T_BIN =? T_STR) with false. cbn [obj_type obj_cnt obj_ptr obj_bodies kids_at obj_cells tl hdr_at tree_wf].
      replace (P_ =? 0) with false by (symmetry; apply Z.eqb_neq; exact P0).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|].
      split; [intros; reflexivity|]. split; [intros a; unfold hdr_at; cbn [obj_type]; tauto|].
      split; [unfold LIMIT; alia|]. split; [intros X; exfalso; exact (P0 X)|]. intros _. split; [exact INZONE| exact RDB].
    - cbn [obj_type obj_cnt obj_ptr obj_bodies kids_at obj_cells tl hdr_at tree_wf].
      replace (SZd - 1 + 1) with SZd by alia. specialize (EXT1 eq_refl).
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact I|].
      split; [intros; reflexivity|]. split; [intros a; unfold hdr_at; cbn [obj_type]; tauto|].
      split; [alia|]. split; [unfold LIMIT; alia|]. split; [exact P0|]. split; [exact INZONE| exact RDB]. }
  destruct OBT as (OBt & OBc & OBp & OBb & OBk & OBcells & OBhdr & OBwf).
  assert (BODIES : bodies_ok z' ls ob).
  { unfold bodies_ok. rewrite OBb. constructor; [|constructor]. unfold range_ok. cbn [fst snd]. split; [alia|]. split; [exact INALLOC| exact RDISJ]. }

  assert (BYA : forall a, P_ <= a < P_ + SZd -> ms_mem ms (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
  { intros a Ha. apply (bytes_of_region segs _ E' (ms_mem ms) kA rA a ROA KA0). rewrite LOA', HIA'. fold P_. alia. }

  set (v0 := Pot.Pot.pot_val ls S0 0) in *.
  assert (V0 : 0 <= v0).
  { subst v0. apply Pot.Pot.pot_val_nonneg; [exact LV| rewrite <- DLEN; exact DLIM| exact (Pot.Pot.kids_pk_nonneg _ _ _ _ KP0)| lia]. }
  assert (DSZ : den E' SZ = den E SZ) by exact (den_reval n0 E E' HX SZ VBSZ).
  assert (POTW : match sc with
                 | Some lo => bv_unsigned (ev E' nP) = v0 + (40 + 4 * SZd) /\ v0 + (40 + 4 * SZd) <= 2 ^ 41 /\
                              POT_BASE <= bv_unsigned (den E' lo) <= POT_BASE + 2 ^ 41 + 2 ^ 21 /\ bv_unsigned (den E' lo) = POT_BASE + v0
                 | None => True end).
  { destruct sc as [lo|]; [| exact I].
    assert (INlo : In lo (op_args o)) by (destruct SCOK as (INP & _); exact (proj1 (INW _ INP))).
    apply (GPot.GPot.sym_word E' E fs aw ws lo nP v0 (40 + 4 * SZd) Pfacts SCOK PRE PA0 (DR lo INlo)); [| alia| alia].
    rewrite EP. subst wP SZd. rewrite DSZ. reflexivity. }
  pose proof (GPot.GPot.scan_oldb E' ws sc SCOK) as OLDB.
  assert (NEWB : match sc with Some _ => POT_BASE <= bv_unsigned (den E' (VP nP GPot.GPot.POT_BASEw)) | None => True end).
  { destruct sc as [lo|]; [| exact I]. destruct POTW as (EVP & VM & _). apply (GPot.GPot.sym_newb E' (Some lo) nP). rewrite EVP. exact VM. }

  assert (EnZP : bv_unsigned (ev E' n0) = zp') by (rewrite EZP, <- DzpS; reflexivity).
  assert (EnZF : bv_unsigned (ev E' nZF) = zf') by (rewrite EZF, <- DzfS; reflexivity).
  set (rZ' := set_cell8 (set_cell8 rZ 2 d2 (VP n0 wzero)) 1 d1 (VP nZF wzero)) in *.
  assert (ROKZ : region_ok segs (s_priv st) E' (ms_mem ms) kZ rZ').
  { subst rZ'. apply (region_ok_set_cell8 segs (s_priv st) E' (ms_mem ms) kZ _ 1%uint63 d1 zfS).
    - apply (region_ok_set_cell8 segs (s_priv st) E' (ms_mem ms) kZ rZ 2%uint63 d2 zpS); [exact ROZ| exact (gran8_find _ _ _ _ GZP)|].
      apply bv_eq. rewrite (den_VP0 E' n0 wzero (weqb_refl _)), EnZP. reflexivity.
    - cbn [set_cell8 rg_cells]. rewrite IMap.find_add_other; [exact (gran8_find _ _ _ _ GZF)| exact (ro_bst _ _ _ _ _ _ ROZ)| intros X; discriminate X].
    - apply bv_eq. rewrite (den_VP0 E' nZF wzero (weqb_refl _)), EnZF. reflexivity. }
  assert (HIZ' : hiZ E' rZ' = hiZ E' rZ /\ loZ rZ' = loZ rZ) by (subst rZ'; split; reflexivity).
  destruct HIZ' as [HIZ' LOZ''].
  assert (INRZ : forall a, inR E' kZ rZ' a -> inR E' kZ rZ a).
  { intros a Ha. unfold inR in Ha |- *. rewrite HIZ', LOZ'' in Ha. exact Ha. }

  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E') ws) a -> FP OPS E' (op_args o) a).
  { intros a RA0 NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E') ws) _ a DEC)). auto. }
  set (KS := [kA; kZ] ++ (if D0b then [] else [kS])) in *.
  set (NR := [(kZ, rZ')]) in *.
  assert (NRcases : forall k r, In (k, r) NR -> k = kZ /\ r = rZ').
  { intros k r Hin. subst NR. destruct Hin as [H1|[]]. injection H1 as <- <-. auto. }
  assert (LENws' : Z.of_nat (length (List.filter (fun w => negb (win3_eqb w (VP kA wzero, SZ, VL (wlit 5)) || negb D0b && win3_eqb w (slot_win kS))) ws)) < two63).
  { pose proof (filter_length_le (fun w => negb (win3_eqb w (VP kA wzero, SZ, VL (wlit 5)) || negb D0b && win3_eqb w (slot_win kS))) ws) as FL.
    unfold two63. clear - FL WLEN. lia. }
  assert (HNDUP : List.NoDup (map fst NR)) by (subst NR; cbn [map fst]; constructor; [intros []| constructor]).
  match goal with |- st_ok _ _ _ (surg _ _ _ (mk_args _ _ (GPot.GPot.pot_sym _ _ ?W) ?CA) (_ ++ ?NF) _) _ _ => set (ws' := W) in *; set (ca' := CA) in *; set (nf := NF) in * end.
  assert (LENP : Z.of_nat (length (GPot.GPot.pot_sym sc nP ws')) < two63) by (unfold GPot.GPot.pot_sym; rewrite GPot.GPot.pot_set_length; exact LENws').

  assert (KEPT : forall w, In w ws' -> In w ws /\ w <> (VP kA wzero, SZ, VL (wlit 5)) /\ (D0b = false -> w <> slot_win kS)).
  { intros w Hw. subst ws'. apply filter_In in Hw as [Hw Q]. apply negb_true_iff in Q. apply orb_false_iff in Q as [Q1 Q2].
    split; [exact Hw|]. split; [intros X; subst w; rewrite win3_eqb_refl in Q1; discriminate Q1|].
    intros XD X; subst w. rewrite XD in Q2. cbn [negb andb] in Q2. rewrite win3_eqb_refl in Q2. discriminate Q2. }
  apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH KS NR _ (GPot.GPot.pot_facts_body sc nP SZ ++ nf) (GPot.GPot.pot_next sc (PrimInt63.add n0 2))).
  -   intros k Hk. subst KS. apply in_app_iff in Hk as [Hk|Hk].
    + destruct Hk as [<-|[<-|[]]]; [split; [exact KA0| exists rA; auto]| split; [exact KZ0| exists rZ; auto]].
    + destruct D0b; [destruct Hk|]. destruct Hk as [<-|[]]. destruct (HD1 eq_refl) as (rS & _ & FS & _ & _ & WS & _ & _ & KS0 & _).
      split; [apply neq_eqb; exact KS0| exists rS; auto].
  -   exact HNDUP.
  -   intros k r Hin. destruct (NRcases k r Hin) as [-> ->]. exact KZ0.
  -   intros k r Hin. destruct (NRcases k r Hin) as [-> ->]. exact ROKZ.
  -   intros k r a Hin IR. destruct (NRcases k r Hin) as [-> ->]. right. exists kZ, rZ. split; [subst KS; right; left; reflexivity|]. split; [exact FZ|]. exact (INRZ a IR).
  -   intros q1 u1 q2 u2 a H1 H2 NE12 _. destruct (NRcases q1 u1 H1) as [-> ->]. destruct (NRcases q2 u2 H2) as [-> ->]. exfalso. exact (NE12 eq_refl).
  -   rewrite (ho_holds _ _ _ _ _ HOPS).
    exists 2, (den E' aw), (map (wden E') (GPot.GPot.pot_sym sc nP ws')), (map (den E') ca'), LB.
    split; [apply mk_args_sound; exact LENP|].

    split; [apply (aw_keep segs IMGX AW _ _ (map (wden E') ws')); [| exact (GPot.GPot.wins_keep_pot_set E' sc _ _ OLDB NEWB LB)];
            apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); apply (UOK.unp_wins_keep_map E' 1 g LB ws ws' P O Wk);
            [intros x Hx; left; exact (proj1 (KEPT x Hx))
            |intros x Hx; destruct (win3_eqb x (VP kA wzero, SZ, VL (wlit 5))) eqn:Q1;
             [right; left; apply win3_eqb_eq in Q1; subst x; apply UOK.kind_sub; vm_compute; reflexivity|];
             destruct (win3_eqb x (slot_win kS)) eqn:Q2;
             [right; left; apply win3_eqb_eq in Q2; subst x; apply UOK.kind_sub; vm_compute; reflexivity|];
             left; subst ws'; apply filter_In; split; [exact Hx|]; cbv beta; rewrite Q1, Q2; rewrite andb_false_r; reflexivity]|]. split.
    +
      apply (GPot.GPot.windows_wf_pot_set E' sc _ _ OLDB NEWB LB _ (aw_ceiling_small segs IMGX AW model)).
      unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
      destruct (KEPT x Hx) as (Hx' & _). exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')).
    +
      cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. subst ca'. cbn [map decode_uc].
      exists g'. split; [| split; [exact PURE'| split; [exact OWNOK'| split; [| split; [| split]]]]].
      *
        enough (LINK' : link (UC (bv_unsigned (den E' root)) (bv_unsigned (den E' cb)) (bv_unsigned (den E' ce)) (bv_unsigned (den E' ccap))
                                (bv_unsigned (den E' vb)) (bv_unsigned (den E' ve)) (bv_unsigned (den E' vcap))
                                (bv_unsigned (den E' (VP n0 wzero))) (bv_unsigned (den E' (VP nZF wzero))) (bv_unsigned (den E' c0))
                                (bv_unsigned (den E' slot)) (bv_unsigned (den E' tD)) (bv_unsigned (den E' restD))
                                (bv_unsigned (den E' (if D0b then tv else rootT))) (bv_unsigned (den E' (if D0b then sv_ext_c false 0%uint63 4%uint63 nsv else n1)))
                                (bv_unsigned (den E' (if D0b then VP kA wzero else P1)))) g') by exact LINK'.
        unfold link. subst g'. cbn [u_root u_vis u_cstk u_vstk u_zone u_levels u_cur_slot c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1].
        rewrite ZCp, ZCf, ZCh.
        split; [exact Lroot|]. split; [exact Lcb|]. split; [exact Lce|]. split; [exact Lccap|]. split; [exact Lvb|]. split; [exact Lve|]. split; [exact Lvcap|].
        split; [symmetry; rewrite (den_VP0 E' n0 wzero (weqb_refl _)); exact EnZP|].
        split; [symmetry; rewrite (den_VP0 E' nZF wzero (weqb_refl _)); exact EnZF|]. split; [exact Lc0|].
        intros NN. fold ls in NN. destruct D0b; [exfalso; exact (NN (DZ eq_refl))|].
        change (u_levels g <> []) in NN. exact (LD NN).
      *
        apply GPot.GPot.wins_ok_pot_set.
        unfold wins_ok in *. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx).
        destruct (KEPT x Hx) as (Hx' & NA & NSW).
        destruct (proj1 (Forall_forall _ _) Wk (wden E' x) (in_map _ _ _ Hx') NS) as [DJ|[NB1 SO]].
        -- left. rewrite OWN'. exact DJ.
        -- right. split; [exact NB1|].
           unfold sub_ok in SO |- *. cbv zeta in SO |- *. subst g'. cbn [u_cstk u_vstk u_levels u_zone].
           destruct SO as [A|[A|[(KD & _)|(KD & _)]]]; [left; exact A| right; left; exact A| exfalso| exfalso].
           ++ destruct D0b; [pose proof (only_kind_sound E' 4 _ ws (HD0 eq_refl) x Hx' KD) as X; discriminate X|].
              destruct (HD1 eq_refl) as (rS & _ & _ & _ & _ & _ & _ & OK4 & _). pose proof (only_kind_sound E' 4 _ ws OK4 x Hx' KD) as X. injection X as <-. exact (NSW eq_refl eq_refl).
           ++ pose proof (only_kind_sound E' 5 _ ws OK5 x Hx' KD) as X. injection X as <-. exact (NA eq_refl).
      *
        destruct M as (M1 & M2 & M3 & M4 & M5 & M6). fold bm ls in M1, M2, M3, M4, M5, M6.
        unfold mem_ok. subst g'. cbn [u_levels u_cstk u_vstk u_zone u_root u_vis]. fold bm. rewrite ZCc.
        split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|]. split; [exact M5|].
        intros l Hl i Hi. destruct (M6 l Hl i Hi) as (ox & T & CSx & BS). exists ox. split; [| split].
        -- eapply tree_at_frame; [apply readable_mono_refl| exact ZG| intros c1 _; apply agree_on_refl| exact T].
        -- intros c1 Hc1. destruct (CSx c1 Hc1) as [A U]. split; [exact (proj2 ZG _ _ A)| exact U].
        -- unfold bodies_ok in *. eapply Forall_impl; [| exact BS]. intros r (R0 & A & U). split; [exact R0|]. split; [exact (proj2 ZG _ _ A)| exact U].
      *
        intros _. cbv zeta. subst g'. cbn [u_levels u_zone u_cur_slot u_root u_vis]. fold ls.
        exists ob. split; [exact OBwf|]. split; [exact OBk|]. split; [| split; [| split; [| split; [| split]]]].
        -- intros NN. apply (proj2 (OBhdr _)). change (cur_slot (u_root g) ls) with (u_cur_slot g).
           destruct D0b; [exfalso; exact (NN (DZ eq_refl))|]. exact (HD1c eq_refl).
        -- intros NIL. cbn [c_rootT c_n1 c_P1]. destruct D0b; [| exfalso; exact (DNZ eq_refl NIL)].
           rewrite OBt, OBc, OBp, TSV, (den_VP0 E' kA wzero (weqb_refl _)), den_sv_ext_c, zx_ext_den, NSV. fold P_.
           repeat split; reflexivity.
        -- intros c Hc. rewrite OBcells in Hc. destruct Hc.
        -- exact BODIES.
        --
           assert (D1 : Cost.obj_depth ob = 1%nat) by (subst ob; destruct isExt; [reflexivity| destruct (t =? T_STR); reflexivity]).
           rewrite D1. pose proof P as (_ & _ & _ & _ & _ & _ & _ & _ & _ & PDL & _ & _). pose proof (Acct.u_D_length g PDL) as UDL. fold ls in UDL. lia.
        --
           exists S0. split.
           ++ apply (Pot.Pot.kids_pk_frame bm bm (u_zone g) z' ls S0); [| exact KP0]. intros l i ox Hl Hi T.
              eapply tree_at_frame; [apply readable_mono_refl| exact ZG| intros c1 _; apply agree_on_refl| exact T].
           ++ apply (GPot.GPot.pot_at_set E' ws ws' sc _ _ SCOK); [intros x Hx; left; exact (proj1 (KEPT x Hx))|].
              destruct sc as [lo|]; [| exact I]. destruct POTW as (EVP & VM & _).
              rewrite (GPot.GPot.pw_den_lo E' nP ltac:(rewrite EVP; exact VM)), EVP.
              rewrite (Pot.Pot.pot_val_item ls S0 (Pot.Pot.pk10_tree ob)). fold v0.
              assert (PKOB : Pot.Pot.pk10_tree ob = 10 + SZd).
              { subst ob. destruct isExt; [rewrite Pot.Pot.pk10_tree_ext; lia|]. destruct (t =? T_STR); [apply Pot.Pot.pk10_tree_str| apply Pot.Pot.pk10_tree_bin]. }
              rewrite PKOB. lia.
      *
        destruct AX as (XA & AA). split.
        { split; [| intros X; discriminate X]. exists XA. subst g'. cbn [u_levels u_zone]. fold ls.
          eapply Acct.acct_frame; [| exact AA]. intros l i ox Hl Hi T.
          eapply tree_at_frame; [apply readable_mono_refl| exact ZG| intros c1 _; apply agree_on_refl| exact T]. }

        apply GPot.GPot.seal_ok_pot_set.
        replace (z_chunks (u_zone g')) with (z_chunks (u_zone g)) by (subst g'; cbn [u_zone]; symmetry; exact ZCc).
        apply (SealX.seal_ok_map _ _ _ _ _ SE). intros x Hx. left. exact (proj1 (KEPT x Hx)).
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 2 _ (map (wden E') (GPot.GPot.pot_sym sc nP ws')) _ a (mk_args_sound E' 2%uint63 aw _ _ LENP))) in FPa as (RA0 & NI & NW).
    assert (NW' : ~ in_ws (map (wden E') ws') a) by (intros X; apply NW; apply GPot.GPot.in_ws_pot_set; exact X). clear NW. rename NW' into NW.
    assert (NWi : forall w, In w ws' -> ~ in_iv (w_iv (wden E' w)) a).
    { intros w Hw Hin. apply NW. apply (proj2 (in_ws_map_iff E' ws' a)). exists w. auto. }
    split.
    + destruct (in_ws_dec (map (wden E') ws) a) as [IW|NIW]; [| left; exact (FPold a RA0 NI NIW)].
      right. apply (proj1 (in_ws_map_iff E' ws a)) in IW as (w & Hw & Hin).
      assert (DEAD : w = (VP kA wzero, SZ, VL (wlit 5)) \/ (D0b = false /\ w = slot_win kS)).
      { destruct (win3_eqb w (VP kA wzero, SZ, VL (wlit 5))) eqn:Q1; [left; exact (win3_eqb_eq _ _ Q1)|].
        destruct (negb D0b && win3_eqb w (slot_win kS)) eqn:Q4.
        - apply andb_prop in Q4 as [Q4 Q5]. right. split; [destruct D0b; [discriminate Q4| reflexivity]| exact (win3_eqb_eq _ _ Q5)].
        - exfalso. apply (NWi w); [| exact Hin]. subst ws'. apply filter_In. split; [exact Hw|]. rewrite Q1, Q4. reflexivity. }
      destruct DEAD as [->|[HD ->]].
      * exists kA, rA. split; [subst KS; left; reflexivity|]. split; [exact FA|].
        unfold wden, w_iv, in_iv in Hin. cbn [w_lo w_len fst snd] in Hin. rewrite (den_VP0 E' kA wzero (weqb_refl _)) in Hin. fold P_ SZd in Hin.
        unfold inR. rewrite LOA', HIA'. fold P_. alia.
      * destruct (HD1 HD) as (rS & SL & FS & LOS & HIS & _). exists kS, rS. split; [subst KS; rewrite HD; apply in_app_iff; right; left; reflexivity|]. split; [exact FS|].
        rewrite slot_win_top, top_win_den in Hin. unfold w_iv, in_iv in Hin. cbn [w_lo w_len fst snd] in Hin. change (to_Z 24%uint63) with 24 in Hin.
        unfold inR, loZ, hiZ. rewrite LOS, HIS. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24. change (keyZ 0%uint63) with 0. alia.
    + intros k r Hin IR. destruct (NRcases k r Hin) as [-> ->].
      apply NW. exfalso. apply (NWi (top_win kZ 56 1)).
      * subst ws'. apply filter_In. split; [exact EXZ|].
        rewrite (G1.win3_eqb_kind_false (top_win kZ 56 1) (VP kA wzero, SZ, VL (wlit 5)) 1 5 eq_refl eq_refl ltac:(clear; lia)).
        destruct D0b; [reflexivity|]. cbn [negb andb orb]. rewrite (G1.win3_eqb_kind_false (top_win kZ 56 1) (slot_win kS) 1 4 eq_refl eq_refl ltac:(clear; lia)). reflexivity.
      * rewrite top_win_den. unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. fold ZB. change (to_Z 56%uint63) with 56.
        unfold inR in IR. rewrite HIZ', LOZ'', LOZ' in IR. unfold hiZ in IR. rewrite HIZ56 in IR. cbn [den] in IR. rewrite wbv_unsigned, wlit_ok in IR.
        change (to_Z 56%uint63) with 56 in IR. fold ZB in IR. alia.
  -
    apply Forall_app. split.
    {
      destruct sc as [lo|]; [| constructor]. destruct POTW as (EVP & VM & B & VLO).
      apply (GPot.GPot.pot_facts_body_hold E' lo nP SZ (v0 + (40 + 4 * SZd)) B EVP); [alia| fold SZd; alia| fold SZd; rewrite VLO; alia]. }
    subst nf. apply Forall_app. split; [| apply Forall_app; split].
    + assert (CHI62 : zp + zf <= two62Z) by (rewrite <- CHI; unfold chunk_hi, CHUNK_HDR, two62Z; alia).
      apply (zp_facts_sound E' fs kA n0 Pfacts). rewrite EnZP, ZP1. fold P_. clear - RSZ ZHI CHI62. unfold two62Z in *. lia.
    + apply (zf_facts_sound E' fs zfree nZF Pfacts). rewrite EnZF, ZFV. clear - ZP1 ZP2 ZLE RSZ RF. lia.
    + constructor; [| constructor; [| constructor]]; cbn [fact_holds];
        replace (bv_unsigned (den E' (VL (wlit 1001)))) with 1001 by (cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
      * fold SZd. exact LIM.
      * rewrite den_sv_ext_c, zx_ext_den, NSV. subst nst. destruct isExt; clear - LIM EXT1 RSZ; lia.
Qed.

Theorem g2b_sound : contract_sound segs OPS MP PB g2b_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [g2b_contract c_apply] in HAP.
  destruct (g2b_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  - exfalso. unfold g2b_apply in AP.
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
  - injection HAP as <-.
    destruct (g2b_sound_main E st ms model st' HS AP) as (E' & HX & HS').
    exact (Hk st' (or_introl eq_refl) E' ms model HX HMP HS').
  - exfalso. unfold g2b_apply in AP.
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End WithPc.
End G2B.
