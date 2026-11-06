(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.

Module GName.

Fixpoint set_nth (i : nat) (v : sv) (l : list sv) : list sv :=
  match l with
  | [] => []
  | x :: t => match i with O => v :: t | S j => x :: set_nth j v t end
  end.

Lemma map_set_nth : forall (f : sv -> bv 64) i v l old, nth_error l i = Some old -> f v = f old -> map f (set_nth i v l) = map f l.
Proof.
  induction i as [|i IH]; intros v l old H EQ; destruct l as [|x t]; cbn in H |- *; try discriminate.
  - injection H as ->. rewrite EQ. reflexivity.
  - rewrite (IH v t old H EQ). reflexivity.
Qed.

Definition name_facts (fs : list fact) (n : int) (old : sv) : list fact :=
  FEq (VP n wzero) old ::
  (let b := sv_bounds fs old in if wltu wzero (fst b) then [FRange n (fst b) (snd b)] else []) ++
  (if aligned fs old 3%uint63 then [FAlign n 3%uint63] else []).

Section WithPc.
Variable S_PC : int.
Variable IDX : nat.

Definition gname_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      match nth_error ca IDX with
      | Some old =>
          let n := s_next st in
          if st_vars_below n st && PrimInt63.ltb 0%uint63 n
          then Some [surg st [] [] (mk_args md aw ws (set_nth IDX (VP n wzero) ca)) (name_facts (s_facts st) n old) (PrimInt63.add n 1%uint63)]
          else None
      | None => None
      end
  | None => None
  end.

Definition gname_contract : contract := Contract S_PC gname_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Theorem gname_sound : contract_sound segs OPS MP PB gname_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS0 HMP HPB Hk. cbn [gname_contract c_apply] in HAP. unfold gname_apply in HAP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (nth_error ca IDX) as [old|] eqn:NTH; [|discriminate].
  match type of HAP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end. injection HAP as <-.
  apply andb_prop in COND as [VB NPOS]. apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS.
  set (n := s_next st) in *.
  set (E' := env_upd E n (den E old)).
  assert (HX : env_ext n E E') by apply env_upd_ext.
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (the_op_full st mdi aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  assert (INo : In old (op_args o)).
  { rewrite ARGS. right; right; right. apply in_app_iff. right. exact (nth_error_In _ _ NTH). }
  pose proof (ops_vars_below n st o VB (op_in_In st o OPS1) old INo) as VBold.
  assert (DOLD : den E' old = den E old) by exact (den_reval n E E' HX old VBold).
  assert (EVn : ev E' n = den E' old) by (rewrite DOLD; apply env_upd_same).
  assert (DN : den E' (VP n wzero) = den E' old) by (apply bv_eq; rewrite (den_VP0 E' n wzero (weqb_refl _)), EVn; reflexivity).
  clearbody E'.
  assert (MAPEQ : map (den E') (set_nth IDX (VP n wzero) ca) = map (den E') ca) by exact (map_set_nth (den E') IDX _ ca old NTH DN).
  refine (Hk _ (or_introl eq_refl) E' ms model HX HMP _).
  apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [] []
           (mk_args mdi aw ws (set_nth IDX (VP n wzero) ca)) (name_facts (s_facts st) n old) (PrimInt63.add n 1)).
  - intros k [].
  - constructor.
  - intros k r [].
  - intros k r [].
  - intros k r a [].
  - intros k1 r1 k2 r2 a [].
  -
    pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
    rewrite (ho_holds _ _ _ _ _ HOPS).
    destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & REST).
    exists md, awZ, wsZ, caZ, LB. split; [| exact REST].
    rewrite (mk_args_sound E' mdi aw ws (set_nth IDX (VP n wzero) ca) LEN), MAPEQ, <- (DECf E'). exact DEC0.
  -
    intros a FPa. split; [| intros k r []]. left. unfold FP in *. rewrite (ho_fp _ _ _ _ _ HOPS) in *.
    apply (proj2 (heap_fp_iff IMGX _ _ _ _ _ a (DECf E'))).
    apply (proj1 (heap_fp_iff IMGX _ _ _ _ _ a (mk_args_sound E' mdi aw ws (set_nth IDX (VP n wzero) ca) LEN))). exact FPa.
  -
    unfold name_facts. constructor.
    + cbn [fact_holds]. exact DN.
    + apply Forall_app. split.
      * pose proof (sv_bounds_sound E' (s_facts st) Pfacts old) as I0. unfold inb in I0.
        destruct (wltu wzero (fst (sv_bounds (s_facts st) old))); [|constructor].
        constructor; [|constructor]. cbn [fact_holds]. rewrite EVn. exact I0.
      * destruct (aligned (s_facts st) old 3%uint63) eqn:AL; [|constructor]. constructor; [|constructor]. cbn [fact_holds]. rewrite EVn.
        exact (aligned_sound E' (s_facts st) Pfacts old 3%uint63 AL ltac:(change (to_Z 3%uint63) with 3; lia)).
Qed.

End Sound.
End WithPc.
End GName.
