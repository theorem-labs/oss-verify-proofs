(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Ops GLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GPot.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UO UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GPotName.

Definition ZHIw : w64 := wlit 2199025352704%uint63.
Definition canonical (lo : sv) : bool := match lo with VP _ o => weqb o GPot.GPot.POT_BASEw | _ => false end.
Definition name_facts (n : int) (lo : sv) : list fact :=
  [FEq (VP n wzero) (sv_alu ALU_ADD lo (VL GPot.GPot.NEG_BASEw)); FRange n wzero ZHIw].

Section WithPc.
Variable S_PC : int.

Definition gpotname_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      match GPot.GPot.pot_scan_c (s_facts st) aw ws with
      | Some (Some lo) =>
          let n := s_next st in
          if negb (canonical lo) && st_vars_below n st && PrimInt63.ltb 0%uint63 n
          then Some [surg st [] [] (mk_args md aw (GPot.GPot.pot_set (Some lo) (VP n GPot.GPot.POT_BASEw) ws) ca) (name_facts n lo) (PrimInt63.add n 1%uint63)]
          else None
      | _ => None
      end
  | None => None
  end.

Definition gpotname_contract : contract := Contract S_PC gpotname_apply.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma map_wden_pot_set : forall E lo lo' ws, den E lo' = den E lo ->
  map (wden E) (GPot.GPot.pot_set (Some lo) lo' ws) = map (wden E) ws.
Proof.
  intros E lo lo' ws EQ. cbn [GPot.GPot.pot_set]. rewrite map_map. apply map_ext_in. intros x _.
  destruct (win3_eqb x (GPot.GPot.pwl lo)) eqn:Q; [| reflexivity]. apply win3_eqb_eq in Q. subst x.
  rewrite !GPot.GPot.pwl_den, EQ. reflexivity.
Qed.

Theorem gpotname_sound : contract_sound segs OPS MP PB gpotname_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS0 HMP HPB Hk. cbn [gpotname_contract c_apply] in HAP. unfold gpotname_apply in HAP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (GPot.GPot.pot_scan_c (s_facts st) aw ws) as [[lo|]|] eqn:SCAN; try discriminate. cbv zeta in HAP.
  match type of HAP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end. injection HAP as <-.
  apply andb_prop in COND as [COND NPOS]. apply andb_prop in COND as [_ VB]. apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS.
  set (n := s_next st) in *.
  set (E' := env_upd E n (Z_to_bv 64 (bv_unsigned (den E lo) - POT_BASE))).
  assert (HX : env_ext n E E') by apply env_upd_ext.
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (the_op_full st mdi aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (GPot.GPot.pot_scan_c_ok E' (s_facts st) aw ws (Some lo) Pfacts SCAN) as (INW & BAND & _).

  assert (INlo : In lo (op_args o)).
  { destruct (in_flat_windows ws _ _ _ INW) as (I1 & _ & _). rewrite ARGS. right; right; right. apply in_app_iff. left. exact I1. }
  pose proof (ops_vars_below n st o VB (op_in_In st o OPS1) lo INlo) as VBlo.
  assert (DLO : den E' lo = den E lo) by exact (den_reval n E E' HX lo VBlo).
  assert (EVn : ev E' n = Z_to_bv 64 (bv_unsigned (den E' lo) - POT_BASE)) by (rewrite DLO; apply env_upd_same).
  assert (EVnZ : bv_unsigned (ev E' n) = bv_unsigned (den E' lo) - POT_BASE).
  { rewrite EVn, Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. unfold POT_BASE, two64 in *. lia. }
  assert (DN : den E' (VP n GPot.GPot.POT_BASEw) = den E' lo).
  { apply bv_eq. rewrite den_VPu, GPot.GPot.POT_BASEw_ok, EVnZ.
    replace (bv_unsigned (den E' lo) - POT_BASE + POT_BASE) with (bv_unsigned (den E' lo)) by lia.
    apply Z.mod_small. pose proof (bv_unsigned_in_range _ (den E' lo)) as R. rewrite bv_modulus_64 in R. exact R. }
  clearbody E'.
  assert (LEN' : Z.of_nat (length (GPot.GPot.pot_set (Some lo) (VP n GPot.GPot.POT_BASEw) ws)) < two63) by (rewrite GPot.GPot.pot_set_length; exact LEN).
  refine (Hk _ (or_introl eq_refl) E' ms model HX HMP _).
  apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [] []
           (mk_args mdi aw (GPot.GPot.pot_set (Some lo) (VP n GPot.GPot.POT_BASEw) ws) ca) (name_facts n lo) (PrimInt63.add n 1)).
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
    rewrite (mk_args_sound E' mdi aw _ ca LEN'), (map_wden_pot_set E' lo _ ws DN). rewrite <- (DECf E'). exact DEC0.
  -
    intros a FPa. split; [| intros k r []]. left. unfold FP in *. rewrite (ho_fp _ _ _ _ _ HOPS) in *.
    apply (proj2 (heap_fp_iff IMGX _ _ _ _ _ a (DECf E'))).
    pose proof (mk_args_sound E' mdi aw _ ca LEN') as MA. rewrite (map_wden_pot_set E' lo _ ws DN) in MA.
    apply (proj1 (heap_fp_iff IMGX _ _ _ _ _ a MA)). exact FPa.
  -
    unfold name_facts. constructor; [| constructor; [| constructor]].
    + cbn [fact_holds]. apply bv_eq. rewrite (den_VP0 E' n wzero (weqb_refl _)), EVnZ, den_sv_alu, GPot.GPot.alu_add_u, den_VL, GPot.GPot.NEG_BASEw_ok.
      pose proof (bv_unsigned_in_range _ (den E' lo)) as R. rewrite bv_modulus_64 in R.
      replace (bv_unsigned (den E' lo) + (two64 - POT_BASE)) with ((bv_unsigned (den E' lo) - POT_BASE) + 1 * two64) by lia.
      rewrite Z.mod_add by (unfold two64; lia). symmetry. apply Z.mod_small. unfold POT_BASE, two64 in *. lia.
    + cbn [fact_holds]. rewrite EVnZ, wzero_ok. change (w2Z ZHIw) with (2 ^ 41 + 2 ^ 21). lia.
Qed.

End Sound.
End WithPc.
End GPotName.
