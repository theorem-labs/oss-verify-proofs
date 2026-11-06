(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia Permutation.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UO UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.

Module GPerm.

Definition reorder (p1 p2 : (sv * sv * sv) -> bool) (ws : list (sv * sv * sv)) : list (sv * sv * sv) :=
  List.filter (fun w => negb (p1 w) && negb (p2 w)) ws ++ List.filter p1 ws ++ List.filter (fun w => negb (p1 w) && p2 w) ws.

Lemma reorder_perm : forall p1 p2 ws, Permutation ws (reorder p1 p2 ws).
Proof.
  intros p1 p2. induction ws as [|a ws IH]; [constructor|]. unfold reorder in *. cbn [List.filter].
  destruct (p1 a) eqn:Q1; cbn [negb andb].
  - apply Permutation_cons_app. exact IH.
  - destruct (p2 a) eqn:Q2; cbn [negb andb].
    + rewrite app_assoc. apply Permutation_cons_app. rewrite <- app_assoc. exact IH.
    + cbn [app]. apply perm_skip. exact IH.
Qed.

Fixpoint wins_eqb (a b : list (sv * sv * sv)) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => win3_eqb x y && wins_eqb a' b'
  | _, _ => false
  end.

Definition linked_to (fs : list fact) (sh k : int) : bool :=
  existsb (fun f => match f with
                    | FEq (VP s o) (VAlu ALU_ADD (VAlu ALU_SRL (VP k' o') (VL c)) (VL _)) =>
                        PrimInt63.eqb s sh && weqb o wzero && PrimInt63.eqb k' k && weqb o' wzero && weqb c (wlit 3%uint63)
                    | _ => false
                    end) fs.
Definition twin_of_carg (i : nat) (fs : list fact) (ca : list sv) (w : (sv * sv * sv)) : bool :=
  match w, nth_error ca i with
  | (VP sh _, _, VL kd), Some (VP k _) => negb (wt kd) && PrimInt63.eqb (wl kd) 9%uint63 && linked_to fs sh k
  | _, _ => false
  end.

Section WithPc.
Variable S_PC : int.
Variable P1 P2 : list fact -> list sv -> (sv * sv * sv) -> bool.

Definition gperm_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 1%uint63 || PrimInt63.eqb md 2%uint63 || PrimInt63.eqb md 3%uint63 then
        let ws' := reorder (P1 (s_facts st) ca) (P2 (s_facts st) ca) ws in
        if wins_eqb ws ws' then None
        else Some [surg st [] [] (mk_args md aw ws' ca) [] (s_next st)]
      else None
  | None => None
  end.

Definition gperm_contract : contract := Contract S_PC gperm_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Hypothesis XW_perm : forall ca LB ws ws' m, Permutation ws ws' -> cw_holds XW 3 ca LB ws m -> cw_holds XW 3 ca LB ws' m.

Lemma in_ws_perm : forall (l l' : list window) a, Permutation l l' -> in_ws l a -> in_ws l' a.
Proof.
  intros l l' a HP H. unfold in_ws in *. apply in_ivs_In in H as (v & Hv & Ha). apply in_ivs_In. exists v. split; [| exact Ha].
  apply in_map_iff in Hv as (w & <- & Hw). apply in_map. exact (Permutation_in _ HP Hw).
Qed.

Theorem gperm_sound : contract_sound segs OPS MP PB gperm_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [gperm_contract c_apply] in HAP. unfold gperm_apply in HAP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 1%uint63 || PrimInt63.eqb mdi 2%uint63 || PrimInt63.eqb mdi 3%uint63) eqn:MD; [|discriminate].
  cbv zeta in HAP.
  set (ws' := reorder (P1 (s_facts st) ca) (P2 (s_facts st) ca) ws) in *.
  destruct (wins_eqb ws ws'); [discriminate|]. injection HAP as <-.
  assert (PERM : Permutation ws ws') by apply reorder_perm.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (the_op_full st mdi aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  assert (LEN' : Z.of_nat (length ws') < two63) by (rewrite <- (Permutation_length PERM); exact LEN).
  assert (PERMZ : Permutation (map (wden E) ws) (map (wden E) ws')) by (apply Permutation_map; exact PERM).
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl _ _) HMP _).
  apply (surgery_sound segs OPS E (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [] []
           (mk_args mdi aw ws' ca) [] (s_next st)).
  - intros k [].
  - constructor.
  - intros k r [].
  - intros k r [].
  - intros k r a [].
  - intros k1 r1 k2 r2 a [].
  -
    pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
    rewrite (ho_holds _ _ _ _ _ HOPS).
    destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
    rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-.
    exists (to_Z mdi), (den E aw), (map (wden E) ws'), (map (den E) ca), LB.
    split; [exact (mk_args_sound E mdi aw ws' ca LEN')|].
    split; [apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA); apply wins_keep_same; intros w; split; intros Hw;
            [exact (Permutation.Permutation_in w (Permutation.Permutation_sym PERMZ) Hw)| exact (Permutation.Permutation_in w PERMZ Hw)]|]. split.
    + unfold windows_wf in *. exact (Permutation_Forall PERMZ WF).
    + cbn [cw_holds unp_cw] in HC |- *. unfold cw_unp_holds in *.
      assert (MDV : to_Z mdi = 1 \/ to_Z mdi = 2 \/ to_Z mdi = 3).
      { apply orb_prop in MD as [MD|Q]; [apply orb_prop in MD as [Q|Q]|]; apply Uint63.eqb_correct in Q; subst mdi; [left| right; left| right; right]; reflexivity. }
      destruct MDV as [M|[M|M]]; rewrite M in HC |- *; cbn [CM_NONE CM_UNP CM_CONS Z.eqb Pos.eqb orb] in HC |- *;
        [ | | exact (XW_perm _ LB _ _ _ PERMZ HC)];
        (destruct (decode_uc (map (den E) ca)) as [u|]; [| exact HC]);
        destruct HC as (g & L & P & O & Wk & MC & CSC & AXC & SE); exists g; (split; [exact L|]); (split; [exact P|]); (split; [exact O|]);
        (assert (NP : forall w, In w (map (wden E) ws') -> pot_win w -> In w (map (wden E) ws))
           by (intros w Hw _; exact (Permutation.Permutation_in w (Permutation.Permutation_sym PERMZ) Hw)));
        (split; [unfold wins_ok in *; exact (Permutation_Forall PERMZ Wk)|]); (split; [exact MC|]); (split; [exact (cons_ok_ws _ _ _ _ _ _ CSC NP)|]); (split; [exact (acct_pot_ws _ _ _ _ _ AXC NP)|]);

        apply (Seal.seal_ok_ws _ _ _ SE); intros w Hw _; exact (Permutation.Permutation_in w (Permutation.Permutation_sym PERMZ) Hw).
  -
    intros a FPa. split; [| intros k r []]. left. unfold FP in *. rewrite (ho_fp _ _ _ _ _ HOPS) in *.
    apply (proj2 (heap_fp_iff IMGX _ _ _ _ _ a (DECf E))).
    apply (proj1 (heap_fp_iff IMGX _ _ _ _ _ a (mk_args_sound E mdi aw ws' ca LEN'))) in FPa as (RA & NI & NW).
    split; [exact RA|]. split; [exact NI|]. intros X. apply NW. exact (in_ws_perm _ _ a PERMZ X).
  - constructor.
Qed.

End Sound.
End WithPc.

Definition is_kind (kd : int) (_ : list fact) (_ : list sv) (w : sv * sv * sv) : bool :=
  match w with (_, _, VL k) => negb (wt k) && PrimInt63.eqb (wl k) kd | _ => false end.
Definition gperm_kinds_contract (pc k1 k2 : int) : contract := gperm_contract pc (is_kind k1) (is_kind k2).

Definition gperm_vec_contract (pc : int) : contract := gperm_contract pc (twin_of_carg 4%nat) (twin_of_carg 1%nat).

End GPerm.
