(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp GWin GWinA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU GW GWA.
Open Scope Z_scope.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GAncA.

Definition eight : w64 := wlit 8%uint63.

Definition topw (k : int) : sv * sv * sv := (VP k wzero, VL eight, VL (wlit 2%uint63)).

Definition resp (kB n : int) (v : sv) : sv :=
  match v with
  | VP k o => if PrimInt63.eqb k kB && weqb o eight then VP n eight else v
  | _ => v
  end.

Definition rewin (kB n : int) (w : sv * sv * sv) : sv * sv * sv :=
  if win3_eqb w (topw kB) then topw n else w.

Definition not_unk (b : bg) : bool := match b with BGUnk => false | _ => true end.

Definition anc_facts (fs : list fact) (cb : sv) (kB n : int) : list fact :=
  FULe cb (VP n wzero) :: FULe (VP n wzero) cb ::
  (let b := sv_bounds fs (VP kB wzero) in if wltu wzero (fst b) then [FRange n (fst b) (snd b)] else []) ++
  (if aligned fs (VP kB wzero) 3%uint63 then [FAlign n 3%uint63] else []).

Definition ord_facts (fs : list fact) (cb ccap : sv) (kB n : int) : list fact :=
  (match decide_ltu_t fs cb (VP kB eight) with Some true => [FULt cb (VP n eight)] | _ => [] end) ++
  (match decide_ltu_t fs (VP kB eight) ccap with Some true => [FULt (VP n eight) ccap] | _ => [] end) ++
  (if has_fact (FULe (VP kB eight) ccap) fs then [FULe (VP n eight) ccap] else []).

Section WithPc.
Variable ANC_PC : int.

Definition ganca_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 then
        match ca with
        | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
            match cb, ce with
            | VP kB ob, VP kB' oe =>
                if weqb ob wzero && PrimInt63.eqb kB' kB && weqb oe eight && negb (PrimInt63.eqb kB 0%uint63)
                   && existsb (win3_eqb (topw kB)) ws then
                  match IMap.find kB (s_regs st) with
                  | Some r =>
                      let n := s_next st in
                      if st_vars_below n st && PrimInt63.ltb 0%uint63 n && rg_w r && PrimInt63.eqb (rg_lo r) 0%uint63
                         && sv_eqb (rg_hi r) (VL eight) && not_unk (rg_bg r)
                      then
                        let ca' := [root; cb; VP n eight; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] in
                        let ws' := List.map (rewin kB n) ws in
                        let nf := anc_facts (s_facts st) cb kB n ++ ord_facts (s_facts st) cb ccap kB n in
                        let st1 := surg st [kB] [(n, r)] (mk_args md aw ws' ca') nf (PrimInt63.add n 1%uint63) in
                        Some [setregs st1 (subst_all (resp kB n) (s_regs st1))]
                      else None
                  | None => None
                  end
                else None
            | _, _ => None
            end
        | _ => None
        end
      else None
  | None => None
  end.

Definition ganca_contract : contract := Contract ANC_PC ganca_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma region_ok_rekey : forall priv E m k n r,
  region_ok segs priv E m k r -> PrimInt63.eqb k 0%uint63 = false -> PrimInt63.eqb n 0%uint63 = false ->
  ev E n = ev E k -> not_unk (rg_bg r) = true -> region_ok segs priv E m n r.
Proof.
  intros priv E m k n r RO K0 N0 EV NU.
  constructor.
  - exact (ro_bst _ _ _ _ _ _ RO).
  - intros _. rewrite EV. exact (ro_range _ _ _ _ _ _ RO K0).
  - intros _ a Ha. rewrite EV in Ha. exact (ro_valid _ _ _ _ _ _ RO K0 a Ha).
  - intros g gr F. rewrite EV. exact (ro_cells _ _ _ _ _ _ RO g gr F).
  - intros g gr c i F Hc Hi. split; [| intros NN; rewrite N0 in NN; discriminate].
    intros _. exact (proj1 (ro_cells_in _ _ _ _ _ _ RO g gr c i F Hc Hi) K0).
  - intros o H1 H2 UC. rewrite EV.
    assert (BG : bg_byte segs E n r o = bg_byte segs E k r o).
    { unfold bg_byte. destruct (rg_bg r); try reflexivity. discriminate NU. }
    rewrite BG. apply (ro_bg _ _ _ _ _ _ RO o); [intros _; exact (H1 N0)| intros KK; rewrite K0 in KK; discriminate| exact UC].
Qed.

Lemma has_fact_holds : forall E f fs, facts_hold E fs -> has_fact f fs = true -> fact_holds E f.
Proof.
  intros E f fs HF. induction fs as [|g fs IH]; cbn [has_fact]; intros H; [discriminate|].
  inversion HF as [|? ? Hg HT]; subst.
  destruct (fact_eqb f g) eqn:Q; [apply fact_eqb_eq in Q; subst; exact Hg| exact (IH HT H)].
Qed.

Lemma ord_facts_sound : forall E fs cb ccap kB n,
  facts_hold E fs -> ev E n = ev E kB -> Forall (fact_holds E) (ord_facts fs cb ccap kB n).
Proof.
  intros E fs cb ccap kB n HF EV.
  assert (D8 : den E (VP n eight) = den E (VP kB eight)).
  { apply bv_eq. rewrite !den_VP, EV. reflexivity. }
  unfold ord_facts. apply Forall_app. split; [| apply Forall_app; split].
  - destruct (decide_ltu_t fs cb (VP kB eight)) as [[|]|] eqn:D; try constructor; [| constructor].
    cbn [fact_holds]. rewrite D8. pose proof (decide_ltu_t_sound E fs HF _ _ _ D) as L. apply (proj1 (ltu_iff _ _ true)) in L. exact L.
  - destruct (decide_ltu_t fs (VP kB eight) ccap) as [[|]|] eqn:D; try constructor; [| constructor].
    cbn [fact_holds]. rewrite D8. pose proof (decide_ltu_t_sound E fs HF _ _ _ D) as L. apply (proj1 (ltu_iff _ _ true)) in L. exact L.
  - destruct (has_fact (FULe (VP kB eight) ccap) fs) eqn:HFc; [| constructor]. constructor; [| constructor].
    cbn [fact_holds]. rewrite D8.
    exact (has_fact_holds E _ fs HF HFc).
Qed.

Lemma rewin_den : forall E kB n w, ev E n = ev E kB -> wden E (rewin kB n w) = wden E w.
Proof.
  intros E kB n w EV. unfold rewin. destruct (win3_eqb w (topw kB)) eqn:Q; [|reflexivity].
  apply win3_eqb_eq in Q. subst w. unfold topw, wden. rewrite !(den_VP0 E _ wzero (weqb_refl _)), EV. reflexivity.
Qed.

Lemma resp_den : forall E kB n v, ev E n = ev E kB -> den E (resp kB n v) = den E v.
Proof.
  intros E kB n v EV. destruct v as [|k o| | | | | | | | |]; try reflexivity. cbn [resp].
  destruct (PrimInt63.eqb k kB && weqb o eight) eqn:Q; [|reflexivity].
  apply andb_prop in Q as [Q1 Q2]. apply Uint63.eqb_correct in Q1. apply weqb_eq in Q2. subst.
  apply bv_eq. rewrite !den_VP, EV. reflexivity.
Qed.

Theorem ganca_sound : contract_sound segs OPS MP PB ganca_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS0 HMP HPB Hk. cbn [ganca_contract c_apply] in HAP. unfold ganca_apply in HAP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1%uint63) eqn:MD; [|discriminate].
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|xx yy]]]]]]]]]]]]]]]]]]; try discriminate.
  destruct cb as [|kB ob| | | | | | | | |]; try discriminate.
  destruct ce as [|kB' oe| | | | | | | | |]; try discriminate.
  match type of HAP with (if ?c then _ else _) = _ => destruct c eqn:C1; [|discriminate] end.
  destruct (IMap.find kB (s_regs st)) as [r|] eqn:FR; [|discriminate].
  match type of HAP with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  injection HAP as <-.
  apply andb_prop in C1 as [C1 EXW]. apply andb_prop in C1 as [C1 KB0]. apply andb_prop in C1 as [C1 OE]. apply andb_prop in C1 as [OB KB'].
  apply Uint63.eqb_correct in KB'. subst kB'. apply negb_true_iff in KB0. apply weqb_eq in OE. subst oe.
  apply andb_prop in C2 as [C2 NU]. apply andb_prop in C2 as [C2 HI]. apply andb_prop in C2 as [C2 LO]. apply andb_prop in C2 as [C2 W].
  apply andb_prop in C2 as [VB NPOS].
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS.
  set (n := s_next st) in *.
  assert (N0 : PrimInt63.eqb n 0%uint63 = false).
  { apply Uint63.eqb_false_spec. intros Q. apply (f_equal to_Z) in Q. change (to_Z 0%uint63) with 0 in Q. lia. }
  set (E' := env_upd E n (ev E kB)).
  assert (HX : env_ext n E E') by apply env_upd_ext.
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
  assert (EVn : ev E' n = ev E' kB).
  { subst E'. rewrite env_upd_same. rewrite ev_upd. destruct (PrimInt63.eqb kB n); reflexivity. }
  clearbody E'.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (the_op_full st mdi aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  set (ca' := [root; VP kB ob; VP n eight; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]) in *.
  set (ws' := List.map (rewin kB n) ws) in *.
  assert (CAEQ : map (den E') ca' = map (den E') [root; VP kB ob; VP kB eight; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]).
  { subst ca'. cbn [map]. do 2 f_equal. f_equal. apply bv_eq. rewrite !den_VP, EVn. reflexivity. }
  assert (WSEQ : map (wden E') ws' = map (wden E') ws).
  { subst ws'. rewrite map_map. apply map_ext_in. intros w _. exact (rewin_den E' kB n w EVn). }
  assert (LEN' : Z.of_nat (length ws') < two63) by (subst ws'; rewrite length_map; exact LEN).
  assert (DEC' : decode (map (den E') (mk_args mdi aw ws' ca')) = decode (map (den E') (op_args o))).
  { rewrite (mk_args_sound E' mdi aw ws' ca' LEN'), WSEQ, CAEQ, <- (DECf E'). reflexivity. }
  refine (Hk _ (or_introl eq_refl) E' ms model HX HMP _). cbv zeta.
  match goal with |- st_ok _ _ _ (setregs ?S1 (subst_all ?F _)) _ _ =>
    change (st_ok segs OPS E' (setregs S1 (subst_all F (s_regs S1))) ms model);
    apply (GWA.st_ok_subst_cells_all segs OPS E' S1 ms model F) end.
  2:{ intros v. exact (resp_den E' kB n v EVn). }
  apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH
           [kB] [(n, r)] (mk_args mdi aw ws' ca') _ (PrimInt63.add n 1%uint63)).
  -
    intros k [<-|[]]. split; [exact KB0|]. exists r. split; [exact FR| exact W].
  - constructor; [intros []| constructor].
  - intros k r' [H|[]]. injection H as <- <-. exact N0.
  - intros k r' [H|[]]. injection H as <- <-. exact (region_ok_rekey (s_priv st) E' (ms_mem ms) kB n r (Preg kB r FR) KB0 N0 EVn NU).
  - intros k r' a [H|[]] IN. injection H as <- <-. right. exists kB, r. split; [left; reflexivity|]. split; [exact FR|].
    unfold inR in *. rewrite EVn in IN. exact IN.
  - intros k1 r1 k2 r2 a [H1|[]] [H2|[]] NE. injection H1 as <- <-. injection H2 as <- <-. exfalso. exact (NE eq_refl).
  -
    pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
    rewrite (ho_holds _ _ _ _ _ HOPS).
    destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & REST).
    exists md, awZ, wsZ, caZ, LB. split; [| exact REST]. rewrite DEC'. exact DEC0.
  -
    intros a FPa.
    assert (FPo : FP OPS E' (op_args o) a).
    { unfold FP in *. rewrite (ho_fp _ _ _ _ _ HOPS) in *.
      apply (proj2 (heap_fp_iff IMGX _ _ _ _ _ a (DECf E'))).
      pose proof (mk_args_sound E' mdi aw ws' ca' LEN') as MK. rewrite WSEQ, CAEQ in MK.
      exact (proj1 (heap_fp_iff IMGX _ _ _ _ _ a MK) FPa). }
    split; [left; exact FPo|].
    intros k r' [H|[]] IN. injection H as <- <-.
    apply (proj1 (old_apart segs OPS E' st ms model o HS opre opost OPSEQ OID a FPo)).
    exists kB, r. split; [exact FR|]. split; [exact KB0|]. unfold inR in IN. rewrite EVn in IN. exact IN.
  -
    assert (DN : den E' (VP n wzero) = den E' (VP kB wzero)) by (apply bv_eq; rewrite !den_VP, EVn; reflexivity).
    assert (DCB : bv_unsigned (den E' (VP kB ob)) = bv_unsigned (den E' (VP n wzero))).
    { rewrite (den_VP0 E' kB ob OB), (den_VP0 E' n wzero (weqb_refl _)), EVn. reflexivity. }
    unfold anc_facts. cbn [app].
    constructor; [cbn [fact_holds]; rewrite DCB; lia|]. constructor; [cbn [fact_holds]; rewrite DCB; lia|].
    apply Forall_app. split; [| exact (ord_facts_sound E' (s_facts st) (VP kB ob) ccap kB n Pfacts EVn)].
    apply Forall_app. split.
    + pose proof (sv_bounds_sound E' (s_facts st) Pfacts (VP kB wzero)) as I0. unfold inb in I0.
      match goal with |- Forall _ (if ?c then _ else _) => destruct c end; [|constructor].
      constructor; [|constructor]. cbn [fact_holds]. rewrite <- (den_VP0 E' n wzero (weqb_refl _)), DN. exact I0.
    + match goal with |- Forall _ (if ?c then _ else _) => destruct c eqn:AL end; [|constructor]. constructor; [|constructor]. cbn [fact_holds].
      rewrite <- (den_VP0 E' n wzero (weqb_refl _)), DN.
      exact (aligned_sound E' (s_facts st) Pfacts (VP kB wzero) 3%uint63 AL ltac:(change (to_Z 3%uint63) with 3; lia)).
Qed.

End Sound.
End WithPc.
End GAncA.

