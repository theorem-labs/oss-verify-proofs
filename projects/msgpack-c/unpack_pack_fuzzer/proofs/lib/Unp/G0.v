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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp G3 GWin.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GPot.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import LiaFast.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 GW.
Open Scope Z_scope.
Unset Lia Cache.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module G0.

Definition block_win (w : sv * sv * sv) : option (int * sv) :=
  match w with
  | (VP k o, len, VL kd) => if weqb o wzero && negb (PrimInt63.eqb k 0%uint63) && negb (wt kd) && PrimInt63.eqb (wl kd) 1%uint63
                           then Some (k, len) else None
  | _ => None
  end.

Definition win_ok0 (fs : list fact) (R : IMap.t region) (w : sv * sv * sv) : bool :=
  match kind_of w with
  | Some 0 => true
  | Some 1 => match block_win w with
              | Some (k, len) => match IMap.find k R with
                                 | Some r => PrimInt63.eqb (rg_lo r) 0%uint63
                                             && match decide_ltu fs (VL wzero) (rg_hi r) with Some true => true | _ => false end
                                 | None => false
                                 end
              | None => false
              end
  | _ => false
  end.

Fixpoint anchors (ws : list (sv * sv * sv)) : list int :=
  match ws with [] => [] | w :: ws' => match block_win w with Some (k, _) => k :: anchors ws' | None => anchors ws' end end.
Fixpoint int_notin (k : int) (l : list int) : bool :=
  match l with [] => true | x :: l' => negb (PrimInt63.eqb k x) && int_notin k l' end.
Fixpoint int_nodupb (l : list int) : bool :=
  match l with [] => true | x :: l' => int_notin x l' && int_nodupb l' end.

Definition soff (o : w64) : option Z := match okey o with Some key => Some (keyZ key) | None => None end.

Section WithPc.
Variable INIT_PC : int.

Definition g0_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 0%uint63 && match ca with [] => true | _ => false end then
      let fs := s_facts st in let n0 := s_next st in let R := s_regs st in
      match getr st X10 with
      | VP k1 octx =>
          match soff octx, IMap.find k1 R with
          | Some xo, Some r1 =>
              match cell_at r1 (xo + 32) 8%uint63, cell_at r1 (xo + 40) 8%uint63, cell_at r1 (xo + 48) 8%uint63, cell_at r1 (xo + 56) 8%uint63 with
              | Some (VP kCB ocb as cb), Some ce, Some (VP kCB' occ as ccap), Some (VP k1' ovis) =>
                  match soff ovis with
                  | Some vo =>
                      match cell_at r1 (vo + 88) 8%uint63, cell_at r1 (vo + 96) 8%uint63, cell_at r1 (vo + 104) 8%uint63, cell_at r1 (vo + 112) 8%uint63 with
                      | Some (VP kVB ovb as vb), Some (VP kVB' ove), Some (VP kVB'' ovc as vcap), Some (VP kZ ozn) =>
                          let root := VP k1 (wadd ovis (wlit 64%uint63)) in
                          match IMap.find kZ R, IMap.find kVB R, IMap.find kCB R with
                          | Some rZ, Some rVB, Some rCB =>
                              match gran8 rZ 1%uint63, gran8 rZ 2%uint63, gran8 rZ 3%uint63, cell_at rVB 0 8%uint63 with
                              | Some (_, VL zf), Some (d2, VP kC0 oc8), Some (_, VP kC0' oc0), Some rt =>
                                  match IMap.find kC0 R with
                                  | Some rC0 =>
                                      match cell_at rC0 0 8%uint63 with
                                      | Some (VL nxt) =>
                                      let wZ := top_win kZ 56%uint63 1%uint63 in let wC0 := top_win kC0 8200%uint63 1%uint63 in
                                      let wVB := top_win kVB 256%uint63 1%uint63 in let wCB := top_win kCB 256%uint63 1%uint63 in
                                      if negb (PrimInt63.eqb k1 0%uint63) && PrimInt63.eqb k1' k1 && sv_eqb cb ce
                                         && PrimInt63.eqb kCB' kCB && PrimInt63.eqb kVB' kVB && PrimInt63.eqb kVB'' kVB && PrimInt63.eqb kC0' kC0
                                         && weqb ocb wzero && weqb occ (wlit 256%uint63) && weqb ovb wzero && weqb ove (wlit 8%uint63)
                                         && weqb ovc (wlit 256%uint63) && weqb ozn wzero && weqb oc8 (wlit 8%uint63) && weqb oc0 wzero
                                         && weqb zf (wlit 8192%uint63) && weqb nxt wzero && sv_eqb rt root
                                         && negb (PrimInt63.eqb kZ 0%uint63) && negb (PrimInt63.eqb kVB 0%uint63) && negb (PrimInt63.eqb kCB 0%uint63)
                                         && negb (PrimInt63.eqb kC0 0%uint63)
                                         && int_nodupb [k1; kZ; kVB; kCB; kC0]
                                         && forallb (win_ok0 fs R) ws && int_nodupb (anchors ws)
                                         && existsb (win3_eqb wZ) ws && existsb (win3_eqb wC0) ws && existsb (win3_eqb wVB) ws && existsb (win3_eqb wCB) ws
                                         && rg_w rZ && rg_w rVB && rg_w rCB && rg_w rC0
                                         && sv_eqb (rg_hi rZ) (VL (wlit 56%uint63)) && sv_eqb (rg_hi rC0) (VL (wlit 8200%uint63))
                                         && sv_eqb (rg_hi rVB) (VL (wlit 256%uint63)) && sv_eqb (rg_hi rCB) (VL (wlit 256%uint63))
                                         && PrimInt63.leb 3%uint63 (find_align fs kCB) && PrimInt63.leb 3%uint63 (find_align fs kVB)
                                         && PrimInt63.leb 4%uint63 (find_align fs kC0)
                                         && match decide_eq0 fs (VP kZ wzero), decide_eq0 fs (VP kCB wzero), decide_eq0 fs (VP kVB wzero), decide_eq0 fs (VP kC0 wzero) with
                                            | Some false, Some false, Some false, Some false => true | _, _, _, _ => false end
                                         && st_vars_below n0 st && PrimInt63.ltb 0%uint63 n0 && PrimInt63.ltb n0 (PrimInt63.sub bit62i 8%uint63)
                                         && Z.ltb (Z.of_nat (length ws)) 4000
                                         && GPot.GPot.all_not_pot fs ws
                                      then
                                        let nZP := n0 in
                                        let rZ' := set_cell8 rZ 2%uint63 d2 (VP nZP wzero) in
                                        let rV' := region8 [Cell 0%uint63 8%uint63 root] in
                                        let dead (w : sv * sv * sv) := win3_eqb w wC0 || win3_eqb w wVB || win3_eqb w wCB in
                                        let ws' := List.filter (fun w => negb (dead w)) ws ++ [top_win kVB 8%uint63 3%uint63] in
                                        let ca' := [root; cb; cb; ccap; vb; VP kVB (wlit 8%uint63); vcap; VP nZP wzero; VL (wlit 8192%uint63);
                                                    VP kC0 wzero; VL wzero; VL wzero; VL wzero; VL wzero; VL wzero; VL wzero; VP kZ wzero] in
                                        let nf := [FEq (VP nZP wzero) (VP kC0 (wlit 8%uint63)); FAlign nZP 3%uint63] ++ zp_facts fs kC0 nZP in
                                        Some [surg st [kC0; kVB; kCB; kZ] [(kVB, rV'); (kZ, rZ')] (mk_args 1%uint63 aw ws' ca') nf (PrimInt63.add n0 1%uint63)]
                                      else None
                                      | _ => None
                                      end
                                  | None => None
                                  end
                              | _, _, _, _ => None
                              end
                          | _, _, _ => None
                          end
                      | _, _, _, _ => None
                      end
                  | None => None
                  end
              | _, _, _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Definition g0_contract : contract := Contract INIT_PC g0_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma neqb_neq : forall a b, negb (PrimInt63.eqb a b) = true -> a <> b.
Proof. intros a b H. apply negb_true_iff in H. exact (Uint63.eqb_false_correct _ _ H). Qed.
Lemma neq_eqb : forall a b, a <> b -> PrimInt63.eqb a b = false.
Proof. intros a b H. apply (proj2 (Uint63.eqb_false_spec _ _)). exact H. Qed.
Lemma existsb_win_In : forall w ws, existsb (win3_eqb w) ws = true -> In w ws.
Proof.
  intros w ws H. apply existsb_exists in H as (x & Hx & Q).
  assert (E0 : x = w).
  { unfold win3_eqb in Q. destruct w as [[a1 a2] a3]. destruct x as [[b1 b2] b3].
    apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2].
    apply sv_eqb_eq in Q1. apply sv_eqb_eq in Q2. apply sv_eqb_eq in Q3. congruence. }
  subst x. exact Hx.
Qed.
Lemma win3_eqb_anchor_false : forall k1 k2 l1 l2 d1 d2, k1 <> k2 -> win3_eqb (top_win k1 l1 d1) (top_win k2 l2 d2) = false.
Proof.
  intros k1 k2 l1 l2 d1 d2 NE. destruct (win3_eqb (top_win k1 l1 d1) (top_win k2 l2 d2)) eqn:Q; [|reflexivity].
  apply win3_eqb_eq in Q. unfold top_win in Q. injection Q. intros; subst; contradiction.
Qed.
Lemma den_VP_nowrap : forall E k o, bv_unsigned (ev E k) + w2Z o < two64 ->
  bv_unsigned (den E (VP k o)) = bv_unsigned (ev E k) + w2Z o.
Proof.
  intros E k o H. cbn [den]. rewrite bv_add_unsigned, wbv_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
  pose proof (bv_unsigned_in_range _ (ev E k)). pose proof (w2Z_range o). apply Z.mod_small. lia.
Qed.

Lemma int_notin_sound : forall k l, int_notin k l = true -> ~ In k l.
Proof.
  induction l as [|x l IH]; intros H; cbn [int_notin] in H; [intros []|]. apply andb_prop in H as [H1 H2].
  intros [<-|Hin]; [rewrite Uint63.eqb_refl in H1; discriminate| exact (IH H2 Hin)].
Qed.
Lemma int_nodupb_sound : forall l, int_nodupb l = true -> List.NoDup l.
Proof.
  induction l as [|x l IH]; intros H; [constructor|]. cbn [int_nodupb] in H. apply andb_prop in H as [H1 H2].
  constructor; [exact (int_notin_sound _ _ H1)| exact (IH H2)].
Qed.
Lemma block_win_sound : forall w k len, block_win w = Some (k, len) -> w = (VP k wzero, len, VL (wlit 1%uint63)) /\ k <> 0%uint63.
Proof.
  intros [[a b] c] k len H. unfold block_win in H. destruct a as [|k' o| | | | | | | | |]; try discriminate. destruct c as [kd| | | | | | | | | |]; try discriminate.
  destruct (weqb o wzero && negb (PrimInt63.eqb k' 0) && negb (wt kd) && PrimInt63.eqb (wl kd) 1) eqn:Q; [|discriminate]. injection H as <- <-.
  apply andb_prop in Q as [Q K1]. apply andb_prop in Q as [Q T]. apply andb_prop in Q as [O K0].
  apply (proj1 (weqb_ok _ _)) in O. subst o. apply neqb_neq in K0. apply negb_true_iff in T. apply Uint63.eqb_correct in K1.
  split; [| exact K0]. destruct kd as [kt kl]. cbn [wt wl] in T, K1. subst. reflexivity.
Qed.
Lemma anchors_In : forall ws w k len, In w ws -> block_win w = Some (k, len) -> In k (anchors ws).
Proof.
  induction ws as [|x ws IH]; intros w k len Hin Hb; [destruct Hin|]. cbn [anchors].
  destruct Hin as [<-|Hin]; [rewrite Hb; left; reflexivity|].
  destruct (block_win x) as [[k' l']|]; [right|]; exact (IH w k len Hin Hb).
Qed.

Lemma anchors_unique : forall ws w1 w2 k l1 l2, List.NoDup (anchors ws) -> In w1 ws -> In w2 ws ->
  block_win w1 = Some (k, l1) -> block_win w2 = Some (k, l2) -> w1 = w2.
Proof.
  induction ws as [|x ws IH]; intros w1 w2 k l1 l2 ND H1 H2 B1 B2; [destruct H1|].
  cbn [anchors] in ND.
  destruct H1 as [<-|H1]; destruct H2 as [<-|H2].
  - reflexivity.
  - rewrite B1 in ND. inversion ND as [|x' l' NI ND']; subst. exfalso. apply NI. exact (anchors_In ws w2 k l2 H2 B2).
  - rewrite B2 in ND. inversion ND as [|x' l' NI ND']; subst. exfalso. apply NI. exact (anchors_In ws w1 k l1 H1 B1).
  - destruct (block_win x) as [[k' l']|]; [inversion ND; subst|]; eapply IH; eauto.
Qed.

Lemma rdisj_of_bytes : forall a n b k, 0 < n -> 0 < k -> (forall x, in_iv (a, n) x -> ~ in_iv (b, k) x) -> rdisj a n b k.
Proof.
  intros a n b k Hn Hk H. unfold rdisj. destruct (Z.lt_ge_cases a b) as [L|L].
  - destruct (Z.le_gt_cases (a + n) b); [lia|]. exfalso. apply (H b); unfold in_iv; cbn [fst snd]; lia.
  - destruct (Z.le_gt_cases (b + k) a); [lia|]. exfalso. apply (H a); unfold in_iv; cbn [fst snd]; lia.
Qed.

Lemma g0_sound_main : forall E st ms model st',
  st_ok segs OPS E st ms model -> g0_apply st = Some [st'] ->
  exists E', env_ext (s_next st) E E' /\ st_ok segs OPS E' st' ms model.
Proof.
  intros E st ms model st' HS0 AP. unfold g0_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 0 && match ca with [] => true | _ => false end) eqn:MD; [|discriminate].
  apply andb_prop in MD as [MD CA]. apply Uint63.eqb_correct in MD. subst mdi. destruct ca; [|discriminate]. clear CA.
  cbv zeta in AP.
  destruct (getr st X10) as [|k1 octx| | | | | | | | |] eqn:GA0; try discriminate.
  destruct (soff octx) as [xo|] eqn:SX; [|discriminate]. destruct (IMap.find k1 (s_regs st)) as [r1|] eqn:F1; [|discriminate].
  destruct (cell_at r1 (xo + 32) 8) as [cb|] eqn:Ccb; [|discriminate]. destruct cb as [|kCB ocb| | | | | | | | |]; try discriminate.
  destruct (cell_at r1 (xo + 40) 8) as [ce|] eqn:Cce; [|discriminate].
  destruct (cell_at r1 (xo + 48) 8) as [ccap|] eqn:Ccc; [|discriminate]. destruct ccap as [|kCB' occ| | | | | | | | |]; try discriminate.
  destruct (cell_at r1 (xo + 56) 8) as [visp|] eqn:Cvp; [|discriminate]. destruct visp as [|k1' ovis| | | | | | | | |]; try discriminate.
  destruct (soff ovis) as [vo|] eqn:SV; [|discriminate].
  destruct (cell_at r1 (vo + 88) 8) as [vb|] eqn:Cvb; [|discriminate]. destruct vb as [|kVB ovb| | | | | | | | |]; try discriminate.
  destruct (cell_at r1 (vo + 96) 8) as [ve|] eqn:Cve; [|discriminate]. destruct ve as [|kVB' ove| | | | | | | | |]; try discriminate.
  destruct (cell_at r1 (vo + 104) 8) as [vcap|] eqn:Cvc; [|discriminate]. destruct vcap as [|kVB'' ovc| | | | | | | | |]; try discriminate.
  destruct (cell_at r1 (vo + 112) 8) as [zn|] eqn:Czn; [|discriminate]. destruct zn as [|kZ ozn| | | | | | | | |]; try discriminate.
  destruct (IMap.find kZ (s_regs st)) as [rZ|] eqn:FZ; [|discriminate].
  destruct (IMap.find kVB (s_regs st)) as [rVB|] eqn:FVB; [|discriminate].
  destruct (IMap.find kCB (s_regs st)) as [rCB|] eqn:FCB; [|discriminate].
  destruct (gran8 rZ 1) as [[d1 zfv]|] eqn:GZ1; [|discriminate]. destruct zfv as [zf| | | | | | | | | |]; try discriminate.
  destruct (gran8 rZ 2) as [[d2 zpv]|] eqn:GZ2; [|discriminate]. destruct zpv as [|kC0 oc8| | | | | | | | |]; try discriminate.
  destruct (gran8 rZ 3) as [[d3 zhv]|] eqn:GZ3; [|discriminate]. destruct zhv as [|kC0' oc0| | | | | | | | |]; try discriminate.
  destruct (cell_at rVB 0 8) as [rt|] eqn:CRT; [|discriminate].
  destruct (IMap.find kC0 (s_regs st)) as [rC0|] eqn:FC0; [|discriminate].
  destruct (cell_at rC0 0 8) as [nx|] eqn:CNX; [|discriminate]. destruct nx as [nxt| | | | | | | | | |]; try discriminate.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection AP as <-.
  set (n0 := s_next st) in *. set (fs := s_facts st) in *. set (root := VP k1 (wadd ovis (wlit 64))) in *.

  apply andb_prop in COND as [COND NOPOT].
  apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND N62]. apply andb_prop in COND as [COND NPOS]. apply andb_prop in COND as [COND VB].
  apply andb_prop in COND as [COND NZZ]. apply andb_prop in COND as [COND ALC0]. apply andb_prop in COND as [COND ALVB]. apply andb_prop in COND as [COND ALCB].
  apply andb_prop in COND as [COND HICBb]. apply andb_prop in COND as [COND HIVBb]. apply andb_prop in COND as [COND HIC0b]. apply andb_prop in COND as [COND HIZb].
  apply sv_eqb_eq in HICBb. apply sv_eqb_eq in HIVBb. apply sv_eqb_eq in HIC0b. apply sv_eqb_eq in HIZb.
  apply andb_prop in COND as [COND WC0]. apply andb_prop in COND as [COND WCB]. apply andb_prop in COND as [COND WVB]. apply andb_prop in COND as [COND WZ].
  apply andb_prop in COND as [COND EXCB]. apply andb_prop in COND as [COND EXVB]. apply andb_prop in COND as [COND EXC0]. apply andb_prop in COND as [COND EXZ].
  apply andb_prop in COND as [COND NDA]. apply andb_prop in COND as [COND WOK]. apply andb_prop in COND as [COND ND5].
  apply andb_prop in COND as [COND KC00]. apply andb_prop in COND as [COND KCB0]. apply andb_prop in COND as [COND KVB0]. apply andb_prop in COND as [COND KZ0].
  apply andb_prop in COND as [COND RT]. apply andb_prop in COND as [COND NXT]. apply andb_prop in COND as [COND ZF].
  apply andb_prop in COND as [COND OC0]. apply andb_prop in COND as [COND OC8]. apply andb_prop in COND as [COND OZN]. apply andb_prop in COND as [COND OVC].
  apply andb_prop in COND as [COND OVE]. apply andb_prop in COND as [COND OVB]. apply andb_prop in COND as [COND OCC]. apply andb_prop in COND as [COND OCB].
  apply andb_prop in COND as [COND KC0E]. apply andb_prop in COND as [COND KVBE2]. apply andb_prop in COND as [COND KVBE]. apply andb_prop in COND as [COND KCBE].
  apply andb_prop in COND as [COND CBCE]. apply andb_prop in COND as [K10 K1E].
  apply negb_true_iff in K10. apply Uint63.eqb_correct in K1E. subst k1'. apply sv_eqb_eq in CBCE. subst ce.
  apply Uint63.eqb_correct in KCBE. subst kCB'. apply Uint63.eqb_correct in KVBE. subst kVB'. apply Uint63.eqb_correct in KVBE2. subst kVB''.
  apply Uint63.eqb_correct in KC0E. subst kC0'.
  apply (proj1 (weqb_ok _ _)) in OCB. subst ocb. apply (proj1 (weqb_ok _ _)) in OCC. subst occ. apply (proj1 (weqb_ok _ _)) in OVB. subst ovb.
  apply (proj1 (weqb_ok _ _)) in OVE. subst ove. apply (proj1 (weqb_ok _ _)) in OVC. subst ovc. apply (proj1 (weqb_ok _ _)) in OZN. subst ozn.
  apply (proj1 (weqb_ok _ _)) in OC8. subst oc8. apply (proj1 (weqb_ok _ _)) in OC0. subst oc0. apply (proj1 (weqb_ok _ _)) in ZF. subst zf.
  apply (proj1 (weqb_ok _ _)) in NXT. subst nxt. apply sv_eqb_eq in RT. subst rt.
  apply negb_true_iff in KZ0. apply negb_true_iff in KVB0. apply negb_true_iff in KCB0. apply negb_true_iff in KC00.
  apply int_nodupb_sound in ND5. apply int_nodupb_sound in NDA.
  apply existsb_win_In in EXZ. apply existsb_win_In in EXC0. apply existsb_win_In in EXVB. apply existsb_win_In in EXCB.
  apply Z.ltb_lt in WLEN. apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS.
  apply Uint63.ltb_spec in N62. replace (to_Z (PrimInt63.sub bit62i 8%uint63)) with (to_Z bit62i - 8) in N62 by (vm_compute; reflexivity).
  assert (NEQ : kZ <> kVB /\ kZ <> kCB /\ kZ <> kC0 /\ kVB <> kCB /\ kVB <> kC0 /\ kCB <> kC0).
  { inversion ND5 as [|a l A1 ND4]; subst. inversion ND4 as [|b l2 A2 ND3]; subst. inversion ND3 as [|c l3 A3 ND2]; subst. inversion ND2 as [|d l4 A4 ND1]; subst.
    cbn [In] in A2, A3, A4. repeat split; intros X; subst; tauto. }
  destruct NEQ as (NZV & NZC & NZ0 & NVC & NV0 & NC0).

  pose proof HS0 as [_ _ _ _ _ _ _ _ _ Pbst0 _ _ _ _ _ _ _ _].
  destruct (the_op_full st 0%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n0 st o VB (op_in_In st o OPS1)) as VBo.
  assert (INW : forall w, In w ws -> In (fst (fst w)) (op_args o) /\ In (snd (fst w)) (op_args o) /\ In (snd w) (op_args o)).
  { intros [[w1 w2] w3] Hw. destruct (in_flat_windows ws w1 w2 w3 Hw) as (I1 & I2 & I3). rewrite ARGS. cbn [fst snd].
    repeat split; right; right; right; apply in_app_iff; left; assumption. }
  assert (KC0_LT : to_Z kC0 < to_Z n0).
  { pose proof (VBo _ (proj1 (INW _ EXC0))) as X. cbn [fst top_win sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }

  set (wZP := Z_to_bv 64 (bv_unsigned (ev E kC0) + 8)).
  set (E' := env_upd E n0 wZP).
  assert (HX : env_ext n0 E E') by (subst E'; apply env_upd_ext).
  assert (EZP : ev E' n0 = wZP) by (subst E'; apply env_upd_same).
  assert (EVC0 : ev E' kC0 = ev E kC0) by exact (ev_reval n0 E E' HX kC0 ltac:(apply Uint63.ltb_spec; exact KC0_LT)).
  clearbody E'.
  exists E'. split; [exact HX|].
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n0 E E' HX st ms model NPOS VB HS0).
  clear HS0 Pbst0.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & _).
  pose proof (DECf E') as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-.
  pose proof (aw_ceiling_small segs IMGX AW model) as CEIL. unfold two62Z in CEIL.

  set (CB := bv_unsigned (ev E' kCB)) in *. set (VBa := bv_unsigned (ev E' kVB)) in *. set (ZBa := bv_unsigned (ev E' kZ)) in *.
  set (C0 := bv_unsigned (ev E' kC0)) in *. set (bm := bmem_of segs (ms_mem ms)) in *.
  assert (INLB : forall k len kd, In (top_win k len kd) ws -> kd = 1%uint63 -> In (bv_unsigned (ev E' k), to_Z len) LB).
  { intros k len kd Hin ->. pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hin)) as X. rewrite top_win_den in X.
    destruct X as (_ & _ & _ & [[K _]|[[_ B]|[K _]]]).
    - cbn [w_kind] in K. change (to_Z 1%uint63) with 1 in K. unfold K_STACK in K. lia.
    - cbn [w_iv w_lo w_len] in B. exact B.
    - cbn [w_kind] in K. unfold K_SUB in K. change (to_Z 1%uint63) with 1 in K. lia. }
  pose proof (INLB kZ 56%uint63 _ EXZ eq_refl) as LBZ. pose proof (INLB kC0 8200%uint63 _ EXC0 eq_refl) as LBC0.
  pose proof (INLB kVB 256%uint63 _ EXVB eq_refl) as LBVB. pose proof (INLB kCB 256%uint63 _ EXCB eq_refl) as LBCB.
  fold ZBa in LBZ. fold C0 in LBC0. fold VBa in LBVB. fold CB in LBCB.
  change (to_Z 56%uint63) with 56 in LBZ. change (to_Z 8200%uint63) with 8200 in LBC0. change (to_Z 256%uint63) with 256 in LBVB, LBCB.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA LBZ) as (BZ1 & _ & BZ3 & _ & _).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA LBC0) as (BC01 & _ & BC03 & _ & _).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA LBVB) as (BV1 & _ & BV3 & _ & _).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model _ HA LBCB) as (BCB1 & _ & BCB3 & _ & _).
  cbn [fst snd] in BZ1, BZ3, BC01, BC03, BV1, BV3, BCB1, BCB3.

  pose proof (Preg kZ rZ FZ) as ROZ. pose proof (Preg kVB rVB FVB) as ROVB. pose proof (Preg kCB rCB FCB) as ROCB. pose proof (Preg kC0 rC0 FC0) as ROC0.

  assert (WREG : forall w k len, In w ws -> block_win w = Some (k, len) ->
            exists r, IMap.find k (s_regs st) = Some r /\ loZ r = 0 /\ 0 < hiZ E' r /\ PrimInt63.eqb k 0%uint63 = false).
  { intros w k len Hin Hb. pose proof (proj1 (forallb_forall _ _) WOK w Hin) as Q. unfold win_ok0 in Q.
    destruct (block_win_sound w k len Hb) as [EW K0]. rewrite EW in Q. cbn [kind_of] in Q. change (wt (wlit 1)) with false in Q. cbn [negb] in Q.
    change (to_Z (wl (wlit 1%uint63))) with 1 in Q. cbn [Z.eqb Pos.eqb] in Q. rewrite <- EW, Hb in Q.
    destruct (IMap.find k (s_regs st)) as [r|] eqn:F; [|discriminate]. apply andb_prop in Q as [LO NE].
    apply Uint63.eqb_correct in LO. destruct (decide_ltu fs (VL wzero) (rg_hi r)) as [[|]|] eqn:DL; try discriminate.
    pose proof (decide_ltu_sound E' fs Pfacts _ _ _ DL) as LT. apply (proj1 (ltu_iff _ _ true)) in LT. replace (bv_unsigned (den E' (VL wzero))) with 0 in LT by (cbn [den]; rewrite wbv_unsigned; reflexivity).
    exists r. split; [reflexivity|]. split; [unfold loZ; rewrite LO; reflexivity|]. split; [unfold hiZ; exact LT| exact (neq_eqb _ _ K0)]. }
  assert (WDIST : forall w1 w2 k l1 kk l2, In w1 ws -> In w2 ws -> block_win w1 = Some (k, l1) -> block_win w2 = Some (kk, l2) -> k <> kk ->
            (exists r, IMap.find kk (s_regs st) = Some r /\ rg_w r = true) -> bv_unsigned (ev E' k) <> bv_unsigned (ev E' kk)).
  { intros w1 w2 k l1 kk l2 H1 H2 B1 B2 NE (rr & FF & WW) EQ.
    destruct (WREG w1 k l1 H1 B1) as (q1 & G1 & L1 & P1 & Z1). destruct (WREG w2 kk l2 H2 B2) as (q2 & G2 & L2 & P2 & Z2).
    rewrite FF in G2. injection G2 as <-.
    apply (Pdisj k q1 kk rr G1 FF NE Z1 Z2 (or_intror WW) (bv_unsigned (ev E' k))). unfold in_based. rewrite L1, L2, <- EQ. lia. }

  assert (BWZ : block_win (top_win kZ 56 1) = Some (kZ, VL (wlit 56))) by (unfold block_win, top_win; rewrite KZ0; reflexivity).
  assert (BWC0 : block_win (top_win kC0 8200 1) = Some (kC0, VL (wlit 8200))) by (unfold block_win, top_win; rewrite KC00; reflexivity).
  assert (BWVB : block_win (top_win kVB 256 1) = Some (kVB, VL (wlit 256))) by (unfold block_win, top_win; rewrite KVB0; reflexivity).
  assert (BWCB : block_win (top_win kCB 256 1) = Some (kCB, VL (wlit 256))) by (unfold block_win, top_win; rewrite KCB0; reflexivity).
  assert (DISJ : forall w k len b, In w ws -> block_win w = Some (k, len) -> In b [(C0, 8200); (VBa, 256); (CB, 256)] ->
            k <> kC0 -> k <> kVB -> k <> kCB -> forall a, in_iv (bv_unsigned (ev E' k), bv_unsigned (den E' len)) a -> ~ in_iv b a).
  { intros w k len b Hin Hb Hbs N1 N2 N3 a Ha Hb'.
    pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hin)) as X. destruct (block_win_sound w k len Hb) as [EW _]. rewrite EW in X.
    unfold wden in X. rewrite (den_VP0 E' k wzero (weqb_refl _)) in X.
    replace (bv_unsigned (den E' (VL (wlit 1%uint63)))) with 1 in X by (cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
    destruct X as (_ & _ & _ & [[K _]|[[_ INB]|[K _]]]).
    - cbn [w_kind] in K. unfold K_STACK in K. lia.
    - cbn [w_iv w_lo w_len] in INB. destruct Hbs as [<-|[<-|[<-|[]]]].
      + refine (aw_blocks_disj segs IMGX AW _ LB _ (ms_mem ms) model _ _ a HA INB LBC0 _ Ha Hb'). cbn [fst]. exact (WDIST w _ k len kC0 _ Hin EXC0 Hb BWC0 N1 ltac:(exists rC0; auto)).
      + refine (aw_blocks_disj segs IMGX AW _ LB _ (ms_mem ms) model _ _ a HA INB LBVB _ Ha Hb'). cbn [fst]. exact (WDIST w _ k len kVB _ Hin EXVB Hb BWVB N2 ltac:(exists rVB; auto)).
      + refine (aw_blocks_disj segs IMGX AW _ LB _ (ms_mem ms) model _ _ a HA INB LBCB _ Ha Hb'). cbn [fst]. exact (WDIST w _ k len kCB _ Hin EXCB Hb BWCB N3 ltac:(exists rCB; auto)).
    - cbn [w_kind] in K. unfold K_SUB in K. lia. }

  set (ROOT := bv_unsigned (den E' root)).
  set (g0 := mkUnp 0 (ROOT - VIS_OBJ_OFF) 0 0 [] (mkVec CB 0 32 8) (mkVec VBa 1 32 8) (mkZone ZBa [(C0, 8192)] (C0 + 8) 8192)).
  assert (OWN0 : owned g0 = [(CB, 256); (VBa, 256); (C0, 8200)]) by reflexivity.
  assert (NZk : forall k, decide_eq0 fs (VP k wzero) = Some false -> bv_unsigned (ev E' k) <> 0).
  { intros k D X. pose proof (decide_eq0_sound E' fs Pfacts _ _ D) as Q. apply (proj1 (eqb_iff _ _ false)) in Q. apply Q. apply bv_eq.
    rewrite <- (den_VP0 E' k wzero (weqb_refl _)) in X. rewrite X, Z_to_bv_unsigned. reflexivity. }
  destruct (decide_eq0 fs (VP kZ wzero)) as [[|]|] eqn:DZ0; try discriminate.
  destruct (decide_eq0 fs (VP kCB wzero)) as [[|]|] eqn:DCB0; try discriminate.
  destruct (decide_eq0 fs (VP kVB wzero)) as [[|]|] eqn:DVB0; try discriminate.
  destruct (decide_eq0 fs (VP kC0 wzero)) as [[|]|] eqn:DC00; try discriminate.
  pose proof (NZk kZ DZ0) as ZB0. pose proof (NZk kCB DCB0) as CB0. pose proof (NZk kVB DVB0) as VB0. pose proof (NZk kC0 DC00) as C00.
  fold ZBa in ZB0. fold CB in CB0. fold VBa in VB0. fold C0 in C00.
  pose proof (mod8_of_align E' fs kCB Pfacts ALCB) as CB8. pose proof (mod8_of_align E' fs kVB Pfacts ALVB) as VB8.
  pose proof (align_of_find E' fs kC0 4%uint63 Pfacts ALC0 ltac:(change (to_Z 4%uint63) with 4; lia)) as C016. change (2 ^ to_Z 4%uint63) with 16 in C016.
  fold CB in CB8. fold VBa in VB8. fold C0 in C016.
  assert (CAP32 : cap32_b 32 = true) by reflexivity.

  pose proof (ro_range _ _ _ _ _ _ ROC0 KC00) as RC0r.
  destruct (WREG _ kC0 _ EXC0 BWC0) as (rC0' & FC0' & LOC0 & _ & KC0f). rewrite FC0 in FC0'. injection FC0' as <-.
  assert (HIC0 : hiZ E' rC0 = 8200) by (unfold hiZ; rewrite HIC0b; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity). rewrite LOC0, HIC0 in RC0r. fold C0 in RC0r.
  destruct (cell_at_u64 segs _ E' (ms_mem ms) kC0 rC0 0 (VL wzero) ROC0 KC0f ltac:(lia) ltac:(unfold two62Z; lia) CNX) as (ANX & _ & _).
  cbn [den] in ANX. rewrite wbv_unsigned, Z.add_0_r in ANX. change (w2Z wzero) with 0 in ANX. fold C0 bm in ANX.

  destruct (WREG _ kVB _ EXVB BWVB) as (rVB' & FVB' & LOVB & _ & KVBf). rewrite FVB in FVB'. injection FVB' as <-.
  assert (HIVB : hiZ E' rVB = 256) by (unfold hiZ; rewrite HIVBb; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ ROVB KVBf) as RVBr. rewrite LOVB, HIVB in RVBr. fold VBa in RVBr.
  destruct (cell_at_u64 segs _ E' (ms_mem ms) kVB rVB 0 root ROVB KVBf ltac:(lia) ltac:(unfold two62Z; lia) CRT) as (ART & _ & _).
  rewrite Z.add_0_r in ART. fold VBa bm ROOT in ART.
  destruct (WREG _ kCB _ EXCB BWCB) as (rCB' & FCB' & LOCB & _ & KCBf). rewrite FCB in FCB'. injection FCB' as <-.
  assert (HICB : hiZ E' rCB = 256) by (unfold hiZ; rewrite HICBb; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ ROCB KCBf) as RCBr. rewrite LOCB, HICB in RCBr. fold CB in RCBr.
  destruct (WREG _ kZ _ EXZ BWZ) as (rZ'' & FZ' & LOZ & _ & KZf). rewrite FZ in FZ'. injection FZ' as <-.
  assert (HIZ : hiZ E' rZ = 56) by (unfold hiZ; rewrite HIZb; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
  pose proof (ro_range _ _ _ _ _ _ ROZ KZf) as RZr. rewrite LOZ, HIZ in RZr. fold ZBa in RZr.

  assert (OD : ForallOrdPairs (fun b b' => rdisj (fst b) (snd b) (fst b') (snd b')) [(CB, 256); (VBa, 256); (C0, 8200)]).
  { assert (D1 : rdisj CB 256 VBa 256).
    { apply rdisj_of_bytes; [lia| lia|]. intros x Hx. refine (aw_blocks_disj segs IMGX AW _ LB _ (ms_mem ms) model _ _ x HA LBCB LBVB _ Hx). cbn [fst].
      exact (WDIST _ _ kCB _ kVB _ EXCB EXVB BWCB BWVB (fun X => NVC (eq_sym X)) ltac:(exists rVB; auto)). }
    assert (D2 : rdisj CB 256 C0 8200).
    { apply rdisj_of_bytes; [lia| lia|]. intros x Hx. refine (aw_blocks_disj segs IMGX AW _ LB _ (ms_mem ms) model _ _ x HA LBCB LBC0 _ Hx). cbn [fst].
      exact (WDIST _ _ kCB _ kC0 _ EXCB EXC0 BWCB BWC0 (fun X => NC0 X) ltac:(exists rC0; auto)). }
    assert (D3 : rdisj VBa 256 C0 8200).
    { apply rdisj_of_bytes; [lia| lia|]. intros x Hx. refine (aw_blocks_disj segs IMGX AW _ LB _ (ms_mem ms) model _ _ x HA LBVB LBC0 _ Hx). cbn [fst].
      exact (WDIST _ _ kVB _ kC0 _ EXVB EXC0 BWVB BWC0 (fun X => NV0 X) ltac:(exists rC0; auto)). }
    constructor; [| constructor; [| constructor; [constructor| constructor]]].
    - constructor; [exact D1| constructor; [exact D2| constructor]].
    - constructor; [exact D3| constructor]. }
  assert (PURE0 : pure_ok g0).
  { subst g0. unfold pure_ok. cbn [u_cstk u_vstk u_levels u_zone u_D length Z.of_nat]. unfold u_D. cbn [u_levels length Z.of_nat Z.add Pos.add].
    unfold vec_valid. cbn [v_elt v_size v_cap v_begin].
    split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact CAP32|].
    split; [lia|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact CAP32|].
    split; [constructor|]. split; [unfold LIMIT; lia|]. split.
    - split; [intros l []| constructor].
    - unfold zone_valid. cbn [z_chunks z_addr z_ptr z_free hd]. unfold chunk_lo, chunk_hi, CHUNK_HDR, CHUNK_SIZE0. cbn [fst snd].
      split; [discriminate|]. split; [exact ZB0|]. split; [intros c [<-|[]]; cbn [fst snd]; lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      constructor; [constructor| constructor]. }
  assert (OWNOK0 : own_ok g0 LB).
  { split; [| rewrite OWN0; split; [exact OD| left; reflexivity]]. rewrite OWN0. intros b [<-|[<-|[<-|[]]]]; [exact LBCB| exact LBVB| exact LBC0]. }

  assert (EnZP : bv_unsigned (ev E' n0) = C0 + 8).
  { rewrite EZP. unfold wZP. rewrite Z_to_bv_unsigned, <- EVC0. fold C0. unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. clear - RC0r. lia. }
  assert (N00 : PrimInt63.eqb n0 0%uint63 = false) by (apply neq_eqb; intros X; assert (X' := f_equal to_Z X); change (to_Z 0%uint63) with 0 in X'; lia).
  set (rZ' := set_cell8 rZ 2 d2 (VP n0 wzero)) in *.
  set (rV' := region8 [Cell 0%uint63 8%uint63 root]) in *.
  assert (ROKV : region_ok segs (s_priv st) E' (ms_mem ms) kVB rV').
  { apply (region8_u64_ok segs _ E' (ms_mem ms) kVB root ROOT KVBf); fold VBa; [lia| | exact ART| reflexivity].
    intros a Ha. apply (bytes_of_region segs _ E' (ms_mem ms) kVB rVB a ROVB KVBf). rewrite LOVB, HIVB. fold VBa. lia. }
  assert (ROKZ : region_ok segs (s_priv st) E' (ms_mem ms) kZ rZ').
  { subst rZ'. apply (region_ok_set_cell8 segs (s_priv st) E' (ms_mem ms) kZ rZ 2%uint63 d2 (VP kC0 (wlit 8))); [exact ROZ| exact (gran8_find _ _ _ _ GZ2)|].
    apply bv_eq. rewrite (den_VP0 E' n0 wzero (weqb_refl _)), EnZP, (den_VP_nowrap E' kC0 (wlit 8)) by (rewrite wlit_ok; change (to_Z 8%uint63) with 8; fold C0; lia).
    rewrite wlit_ok. reflexivity. }
  assert (HIV8 : hiZ E' rV' = 8 /\ loZ rV' = 0) by (split; [unfold hiZ; cbn [rV' region8 rg_hi den]; rewrite wbv_unsigned, wlit_ok; reflexivity| reflexivity]).
  destruct HIV8 as [HIV8 LOV8].
  assert (HIZ' : hiZ E' rZ' = hiZ E' rZ /\ loZ rZ' = loZ rZ) by (subst rZ'; split; reflexivity). destruct HIZ' as [HIZ' LOZ''].
  assert (FPold : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws (map (wden E') ws) a -> FP OPS E' (op_args o) a).
  { intros a RA0 NI NW. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 0 _ (map (wden E') ws) _ a DEC)). auto. }
  match goal with |- st_ok _ _ _ (surg _ _ _ (mk_args _ _ ?W ?CA) ?NF _) _ _ => set (ws' := W) in *; set (ca' := CA) in *; set (nf := NF) in * end.
  assert (LENws' : Z.of_nat (length ws') < two63).
  { subst ws'. rewrite length_app. cbn [length].
    match goal with |- context [List.filter ?f ws] => pose proof (filter_length_le f ws) end. unfold two63. lia. }
  assert (KEPT : forall w, In w ws' -> (In w ws /\ w <> top_win kC0 8200 1 /\ w <> top_win kVB 256 1 /\ w <> top_win kCB 256 1) \/ w = top_win kVB 8 3).
  { intros w Hw. subst ws'. apply in_app_iff in Hw as [Hw|[<-|[]]]; [left| right; reflexivity].
    apply filter_In in Hw as [Hw Q]. apply negb_true_iff in Q. apply orb_false_iff in Q as [Q Q3]. apply orb_false_iff in Q as [Q1 Q2].
    split; [exact Hw|]. repeat split; intros X; subst w; rewrite win3_eqb_refl in *; discriminate. }
  apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [kC0; kVB; kCB; kZ] [(kVB, rV'); (kZ, rZ')] _ nf (PrimInt63.add n0 1)).
  -   intros k [<-|[<-|[<-|[<-|[]]]]]; [split; [exact KC0f| exists rC0; auto]| split; [exact KVBf| exists rVB; auto]| split; [exact KCBf| exists rCB; auto]| split; [exact KZf| exists rZ; auto]].
  -   cbn [map fst]. constructor; [intros [X|[]]; exact (NZV X)| constructor; [intros []| constructor]].
  -   intros k r [H|[H|[]]]; injection H as <- <-; [exact KVBf| exact KZf].
  -   intros k r [H|[H|[]]]; injection H as <- <-; [exact ROKV| exact ROKZ].
  -   intros k r a [H|[H|[]]] IR; injection H as <- <-; right.
    + exists kVB, rVB. split; [right; left; reflexivity|]. split; [exact FVB|]. unfold inR in IR |- *. rewrite HIV8, LOV8 in IR. rewrite LOVB, HIVB. lia.
    + exists kZ, rZ. split; [right; right; right; left; reflexivity|]. split; [exact FZ|]. unfold inR in IR |- *. rewrite HIZ', LOZ'' in IR. exact IR.
  -   intros k1' r1' k2 r2 a H1 H2 NE12 [I1 I2].
    destruct H1 as [H1|[H1|[]]]; injection H1 as <- <-; destruct H2 as [H2|[H2|[]]]; injection H2 as <- <-; try contradiction.
    + apply (Pdisj kVB rVB kZ rZ FVB FZ (fun X => NZV (eq_sym X)) KVBf KZf (or_introl WVB) a). unfold inR in I1, I2 |- *.
      rewrite HIV8, LOV8 in I1. rewrite HIZ', LOZ'' in I2. rewrite LOVB, HIVB. split; [lia| exact I2].
    + apply (Pdisj kVB rVB kZ rZ FVB FZ (fun X => NZV (eq_sym X)) KVBf KZf (or_introl WVB) a). unfold inR in I1, I2 |- *.
      rewrite HIV8, LOV8 in I2. rewrite HIZ', LOZ'' in I1. rewrite LOVB, HIVB. split; [lia| exact I1].
  -   rewrite (ho_holds _ _ _ _ _ HOPS).
    exists 1, (den E' aw), (map (wden E') ws'), (map (den E') ca'), LB.
    split; [apply mk_args_sound; exact LENws'|].

    split; [apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); apply UOK.wins_keep_map_intro;
            [intros x Hx; destruct (KEPT x Hx) as [(Hx' & _)| ->]; [left; exact Hx'| right; apply UOK.kind_new_sub; vm_compute; reflexivity]
            |intros x Hx;
             destruct (win3_eqb x (top_win kC0 8200 1)) eqn:Q1;
             [right; apply win3_eqb_eq in Q1; subst x; split; [apply UOK.kind_untied; vm_compute; reflexivity|]; intros _ _;
              rewrite top_win_den; apply UOK.block_evidence; cbn [w_iv w_lo w_len]; change (to_Z 8200%uint63) with 8200;
              [fold C0; exact LBC0| unfold c24, C24_LO, C24_HI; lia| lia]|];
             destruct (win3_eqb x (top_win kVB 256 1)) eqn:Q2;
             [right; apply win3_eqb_eq in Q2; subst x; split; [apply UOK.kind_untied; vm_compute; reflexivity|]; intros _ _;
              rewrite top_win_den; apply UOK.block_evidence; cbn [w_iv w_lo w_len]; change (to_Z 256%uint63) with 256;
              [fold VBa; exact LBVB| unfold c24, C24_LO, C24_HI; lia| lia]|];
             destruct (win3_eqb x (top_win kCB 256 1)) eqn:Q3;
             [right; apply win3_eqb_eq in Q3; subst x; split; [apply UOK.kind_untied; vm_compute; reflexivity|]; intros _ _;
              rewrite top_win_den; apply UOK.block_evidence; cbn [w_iv w_lo w_len]; change (to_Z 256%uint63) with 256;
              [fold CB; exact LBCB| unfold c24, C24_LO, C24_HI; lia| lia]|];
             left; subst ws'; apply in_or_app; left; apply filter_In; split; [exact Hx|]; cbv beta; rewrite Q1, Q2, Q3; reflexivity]|]. split.
    + unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
      destruct (KEPT x Hx) as [(Hx' & _)| ->]; [exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx'))|].
      rewrite top_win_den. fold VBa. change (to_Z 8%uint63) with 8. change (to_Z 3%uint63) with 3.
      unfold window_wf. cbn [w_lo w_len w_kind w_iv]. split; [lia|]. split; [lia|]. split; [lia|].
      right; right. split; [unfold K_SUB; lia|]. exists (VBa, 256). split; [exact LBVB|]. intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [fst snd w_lo w_len] in Ha |- *. lia.
    + cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb]. subst ca'. cbn [map decode_uc].
      exists g0. split; [| split; [exact PURE0| split; [exact OWNOK0| split; [| split]]]].
      *
        enough (LINK' : link (UC (bv_unsigned (den E' root)) (bv_unsigned (den E' (VP kCB wzero))) (bv_unsigned (den E' (VP kCB wzero)))
                                (bv_unsigned (den E' (VP kCB (wlit 256)))) (bv_unsigned (den E' (VP kVB wzero))) (bv_unsigned (den E' (VP kVB (wlit 8))))
                                (bv_unsigned (den E' (VP kVB (wlit 256)))) (bv_unsigned (den E' (VP n0 wzero))) (bv_unsigned (den E' (VL (wlit 8192))))
                                (bv_unsigned (den E' (VP kC0 wzero))) (bv_unsigned (den E' (VL wzero))) (bv_unsigned (den E' (VL wzero)))
                                (bv_unsigned (den E' (VL wzero))) (bv_unsigned (den E' (VL wzero))) (bv_unsigned (den E' (VL wzero)))
                                (bv_unsigned (den E' (VL wzero)))) g0) by exact LINK'.
        unfold link. subst g0. cbn [u_root u_vis u_cstk u_vstk u_zone u_levels v_begin v_size v_cap v_elt z_ptr z_free z_chunks c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1]. unfold v_end, v_capend, z_head. cbn [v_begin v_elt v_size v_cap z_chunks].
        unfold u_root. cbn [u_vis]. split; [subst ROOT; unfold VIS_OBJ_OFF; lia|].
        split; [symmetry; exact (den_VP0 E' kCB wzero (weqb_refl _))|]. split; [rewrite (den_VP0 E' kCB wzero (weqb_refl _)); fold CB; lia|].
        split; [rewrite (den_VP_nowrap E' kCB (wlit 256)) by (rewrite wlit_ok; change (to_Z 256%uint63) with 256; fold CB; lia); rewrite wlit_ok; change (to_Z 256%uint63) with 256; fold CB; lia|].
        split; [symmetry; exact (den_VP0 E' kVB wzero (weqb_refl _))|].
        split; [rewrite (den_VP_nowrap E' kVB (wlit 8)) by (rewrite wlit_ok; change (to_Z 8%uint63) with 8; fold VBa; lia); rewrite wlit_ok; change (to_Z 8%uint63) with 8; fold VBa; lia|].
        split; [rewrite (den_VP_nowrap E' kVB (wlit 256)) by (rewrite wlit_ok; change (to_Z 256%uint63) with 256; fold VBa; lia); rewrite wlit_ok; change (to_Z 256%uint63) with 256; fold VBa; lia|].
        split; [rewrite (den_VP0 E' n0 wzero (weqb_refl _)), EnZP; reflexivity|].
        split; [cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity|].
        split; [symmetry; exact (den_VP0 E' kC0 wzero (weqb_refl _))|].
        intros X. exfalso. exact (X eq_refl).
      *
        unfold wins_ok. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx). intros NK.
        destruct (KEPT x Hx) as [(Hx' & N1 & N2 & N3)| ->].
        -- left. rewrite OWN0. pose proof (proj1 (forallb_forall _ _) WOK x Hx') as Q. unfold win_ok0 in Q.
           destruct (kind_of x) as [kd|] eqn:KO; [|discriminate]. pose proof (kind_of_sound E' x kd KO) as KD.
           destruct kd as [|pk|nk]; [exfalso; apply NK; rewrite KD; reflexivity| | discriminate Q].
           destruct pk as [pk'|pk'|]; [discriminate Q| discriminate Q|].
           destruct (block_win x) as [[k len]|] eqn:BW; [|discriminate]. destruct (block_win_sound x k len BW) as [EW K0].
           assert (Nk : k <> kC0 /\ k <> kVB /\ k <> kCB).
           { repeat split; intros ->.
             - apply N1. exact (anchors_unique ws x _ kC0 len _ NDA Hx' EXC0 BW BWC0).
             - apply N2. exact (anchors_unique ws x _ kVB len _ NDA Hx' EXVB BW BWVB).
             - apply N3. exact (anchors_unique ws x _ kCB len _ NDA Hx' EXCB BW BWCB). }
           destruct Nk as (Nk1 & Nk2 & Nk3).
           split; [left; exact KD|].
           intros b Hb a Ha. rewrite EW in Ha. unfold wden, w_iv in Ha. cbn [w_lo w_len] in Ha. rewrite (den_VP0 E' k wzero (weqb_refl _)) in Ha.
           apply (DISJ x k len b Hx' BW); try assumption. revert Hb. cbn [In]. tauto.
        -- right. rewrite top_win_den. fold VBa. change (to_Z 8%uint63) with 8. change (to_Z 3%uint63) with 3. cbn [w_kind]. split; [unfold K_BLOCK; lia|].
           unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. right; left. split; [reflexivity|]. subst g0. cbn [u_vstk]. unfold v_end, v_capend. cbn [v_begin v_elt v_size v_cap]. lia.
      *
        unfold mem_ok. subst g0. cbn [u_levels u_cstk u_vstk u_zone u_root u_vis v_begin z_chunks removelast rev tl containers].
        split; [exact I|]. split; [intros X; exfalso; exact (X eq_refl)|]. split; [exact I|]. split; [| split; [exact I| intros l []]].
        cbn [chunks_at]. split; [exact ANX| exact I].
      *
        split; [intros X; discriminate X|]. split; [split; [exists 0; subst g0; cbn [u_levels u_zone]; apply Acct.acct_nil; lia|]|].
        {
          intros _. exists 0. split; [subst g0; cbn [u_levels u_zone]; apply Pot.Pot.kids_pk_nil|]. apply pot_at_none.
          intros w Hw. apply in_map_iff in Hw as (x & <- & Hx). destruct (KEPT x Hx) as [(Hx' & _)| ->].
          - exact (GPot.GPot.not_pot_sound E' (s_facts st) x Pfacts (GPot.GPot.all_not_pot_In _ _ NOPOT x Hx')).
          - intros (K & _). rewrite top_win_den in K. cbn [w_kind] in K. change (to_Z 3%uint63) with 3 in K. unfold K_STACK in K. lia. }

        apply SealX.seal_ok_no9.
        -- intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx). destruct (KEPT x Hx) as [(Hx' & _)| ->].
           ++ pose proof (proj1 (forallb_forall _ _) WOK x Hx') as Q. unfold win_ok0 in Q.
              destruct (kind_of x) as [kd|] eqn:KO; [|discriminate]. pose proof (kind_of_sound E' x kd KO) as KD. rewrite K9 in KD.
              unfold Seal.K_TWIN in KD. subst kd. discriminate Q.
           ++ rewrite top_win_den in K9. cbn [w_kind] in K9. change (to_Z 3%uint63) with 3 in K9. unfold Seal.K_TWIN in K9. lia.
        -- subst g0. cbn [u_zone z_chunks]. intros c [<-|[]]. reflexivity.
  -
    intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
    apply (proj1 (heap_fp_iff IMGX _ 1 _ (map (wden E') ws') _ a (mk_args_sound E' 1%uint63 aw _ _ LENws'))) in FPa as (RA0 & NI & NW).
    assert (NWi : forall w, In w ws' -> ~ in_iv (w_iv (wden E' w)) a).
    { intros w Hw Hin. apply NW. apply (proj2 (in_ws_map_iff E' ws' a)). exists w. auto. }
    split.
    + destruct (in_ws_dec (map (wden E') ws) a) as [IW|NIW]; [| left; exact (FPold a RA0 NI NIW)].
      right. apply (proj1 (in_ws_map_iff E' ws a)) in IW as (w & Hw & Hin).
      assert (DEAD : w = top_win kC0 8200 1 \/ w = top_win kVB 256 1 \/ w = top_win kCB 256 1).
      { destruct (win3_eqb w (top_win kC0 8200 1)) eqn:Q1; [left; exact (win3_eqb_eq _ _ Q1)|].
        destruct (win3_eqb w (top_win kVB 256 1)) eqn:Q2; [right; left; exact (win3_eqb_eq _ _ Q2)|].
        destruct (win3_eqb w (top_win kCB 256 1)) eqn:Q3; [right; right; exact (win3_eqb_eq _ _ Q3)|].
        exfalso. apply (NWi w); [| exact Hin]. subst ws'. apply in_app_iff. left. apply filter_In. split; [exact Hw|]. rewrite Q1, Q2, Q3. reflexivity. }
      destruct DEAD as [->|[->| ->]]; rewrite top_win_den in Hin; unfold w_iv, in_iv in Hin; cbn [w_lo w_len fst snd] in Hin.
      * exists kC0, rC0. split; [left; reflexivity|]. split; [exact FC0|]. unfold inR. rewrite LOC0, HIC0. fold C0 in Hin |- *. change (to_Z 8200%uint63) with 8200 in Hin. lia.
      * exists kVB, rVB. split; [right; left; reflexivity|]. split; [exact FVB|]. unfold inR. rewrite LOVB, HIVB. fold VBa in Hin |- *. change (to_Z 256%uint63) with 256 in Hin.
        assert (~ (VBa <= a < VBa + 8)); [| lia]. intros X. apply (NWi (top_win kVB 8 3)); [subst ws'; apply in_app_iff; right; left; reflexivity|].
        rewrite top_win_den. unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. fold VBa. change (to_Z 8%uint63) with 8. lia.
      * exists kCB, rCB. split; [right; right; left; reflexivity|]. split; [exact FCB|]. unfold inR. rewrite LOCB, HICB. fold CB in Hin |- *. change (to_Z 256%uint63) with 256 in Hin. lia.
    + intros k r [H|[H|[]]] IR; injection H as <- <-.
      * apply (NWi (top_win kVB 8 3)); [subst ws'; apply in_app_iff; right; left; reflexivity|].
        rewrite top_win_den. unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. fold VBa. change (to_Z 8%uint63) with 8. unfold inR in IR. rewrite HIV8, LOV8 in IR. fold VBa in IR. lia.
      * apply (NWi (top_win kZ 56 1)).
        -- subst ws'. apply in_app_iff. left. apply filter_In. split; [exact EXZ|].
           rewrite (win3_eqb_anchor_false kZ kC0 _ _ _ _ NZ0), (win3_eqb_anchor_false kZ kVB _ _ _ _ NZV), (win3_eqb_anchor_false kZ kCB _ _ _ _ NZC). reflexivity.
        -- rewrite top_win_den. unfold w_iv, in_iv. cbn [w_lo w_len fst snd]. fold ZBa. change (to_Z 56%uint63) with 56.
           unfold inR in IR. rewrite HIZ', LOZ'', LOZ, HIZ in IR. fold ZBa in IR. lia.
  -
    subst nf. constructor.
    { cbn [fact_holds]. apply bv_eq. rewrite (den_VP0 E' n0 wzero (weqb_refl _)), EnZP, (den_VP_nowrap E' kC0 (wlit 8)) by (rewrite wlit_ok; change (to_Z 8%uint63) with 8; fold C0; lia).
      rewrite wlit_ok. reflexivity. }
    constructor.
    { cbn [fact_holds]. change (to_Z 3%uint63) with 3. change (2 ^ 3) with 8. rewrite EnZP.
      apply Z.mod_divide in C016; [|lia]. destruct C016 as [q Hq]. rewrite Hq. replace (q * 16 + 8) with ((2 * q + 1) * 8) by lia. apply Z_mod_mult. }
    apply (zp_facts_sound E' fs kC0 n0 Pfacts). rewrite EnZP. fold C0. unfold two62Z in *. lia.
Qed.

Theorem g0_sound : contract_sound segs OPS MP PB g0_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [g0_contract c_apply] in HAP.
  destruct (g0_apply st) as [[|st' [|? ?]]|] eqn:AP; try discriminate.
  - exfalso. unfold g0_apply in AP.
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
  - injection HAP as <-.
    destruct (g0_sound_main E st ms model st' HS AP) as (E' & HX & HS').
    exact (Hk st' (or_introl eq_refl) E' ms model HX HMP HS').
  - exfalso. unfold g0_apply in AP.
    repeat match type of AP with
    | (match ?x with _ => _ end) = _ => destruct x; try discriminate AP
    | (if ?c then _ else _) = _ => destruct c; try discriminate AP
    end.
Qed.

End Sound.
End WithPc.
End G0.
