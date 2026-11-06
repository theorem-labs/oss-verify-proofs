(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs StepSoundBase StepSoundMem PlanSound Acc StepAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge GLib PkPeek PkStep PkStepA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import AccStep.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS CtrLib UB UG.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module ShLoadLit.
Section WithSegs.
Variable segs : list Segment.
Variable VIDS : list int.
Variable ZW : list (int * int).

Definition in_wins (a : int) : bool := existsb (fun w => PrimInt63.leb (fst w) a && PrimInt63.ltb a (snd w)) ZW.

Definition shloadlit_apply (st : sstate) : option (list sstate) :=
  match PkPeek.load_at segs (s_pc st) with
  | Some (SZ1, sx, rd, rs, off) =>
      match sv_alu ALU_ADD (getr st rs) (VL off) with
      | VL a =>
          if negb (wt a) && in_wins (wl a) && negb (r5_eqb rd X0) && PrimInt63.ltb (s_pc st) bit62i
             && forallb (fun id => match find_op id (s_ops st) with Some _ => true | None => false end) VIDS
          then Some [setpc (setr st rd (VL wzero)) (PrimInt63.add (s_pc st) 4%uint63)]
          else None
      | _ => None
      end
  | _ => None
  end.
Definition shloadlit_c (pc : int) : contract := Contract pc shloadlit_apply.
End WithSegs.

Lemma find_op_in : forall id os args, find_op id os = Some args -> exists o, In o os /\ op_id o = id /\ op_args o = args.
Proof.
  induction os as [|o os IH]; intros args H; cbn [find_op] in H; [discriminate|].
  destruct (PrimInt63.eqb (op_id o) id) eqn:Q.
  - injection H as <-. exists o. split; [left; reflexivity| split; [apply Uint63.eqb_correct; exact Q| reflexivity]].
  - destruct (IH args H) as (o' & I1 & I2 & I3). exists o'. split; [right; exact I1| split; assumption].
Qed.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable VIDS : list int.
Variable ZW : list (int * int).
Variable CHS : list oinst -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis LAWS : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPS mo -> Forall (fun o => op_holds OPS (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CHS os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPS mo' /\
              Forall (fun o => op_holds OPS (fst o) (snd o) m mo') os.

Hypothesis HZ : forall (os : list oinst) m mo a,
  (forall id, In id VIDS -> exists args, In (id, args) os /\ op_holds OPS id args m mo) -> in_wins ZW a = true ->
  m (Z_to_bv 64 (to_Z a)) = Some (Z_to_bv 8 0) /\ CHS os m mo (to_Z a).
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma shloadlit_sound_main : forall E st ms model sts,
  st_ok segs OPS E st ms model -> MP model -> shloadlit_apply segs VIDS ZW st = Some sts ->
  exists st' ms' mo', sts = [st'] /\ mi_account_step segs ms model = MachineOk (ms', mo') /\ ms_mem ms' = ms_mem ms /\
                      st_ok segs OPS E st' ms' mo' /\ MP mo'.
Proof.
  intros E st ms model sts HS HMP AP. unfold shloadlit_apply in AP.
  destruct (PkPeek.load_at segs (s_pc st)) as [[[[[sz sx] rd] rs] off]|] eqn:LA; [|discriminate].
  destruct sz; try discriminate.
  destruct (sv_alu ALU_ADD (getr st rs) (VL off)) as [a| | | | | | | | | |] eqn:AD; try discriminate.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end. injection AP as <-.
  apply andb_prop in C as [C FO]. apply andb_prop in C as [C PCB]. apply andb_prop in C as [C RDX]. apply andb_prop in C as [WT INW].
  apply negb_true_iff in WT.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (PRES : forall id, In id VIDS -> exists args, In (id, args) (insts E (s_ops st)) /\ op_holds OPS id args (ms_mem ms) model).
  { intros id Hid. pose proof (proj1 (forallb_forall _ _) FO id Hid) as F1. cbn beta in F1.
    destruct (find_op id (s_ops st)) as [zargs|] eqn:FZ; [|discriminate F1].
    destruct (find_op_in id (s_ops st) zargs FZ) as (o & OIN & OID & OARGS).
    exists (map (den E) (op_args o)). split.
    - unfold insts. apply in_map_iff. exists o. split; [rewrite OID; reflexivity| exact OIN].
    - pose proof (ops_hold_in OPS _ _ _ _ o Pops OIN) as OH. rewrite OID in OH. exact OH. }
  destruct (PkPeek.load_at_spec segs (s_pc st) _ _ _ _ _ LA) as (w & i & FW & EC & DA & OI). rewrite <- Ppc in FW.
  destruct (HZ (insts E (s_ops st)) (ms_mem ms) model (wl a) PRES INW) as [BYTE CH].
  assert (AV : w2Z a = to_Z (wl a)) by (unfold w2Z; rewrite WT; reflexivity).
  pose proof (to_Z_bounded (wl a)) as RA. rewrite wB_two63 in RA.
  assert (HAD : den E (sv_alu ALU_ADD (getr st rs) (VL off)) = Z_to_bv 64 (to_Z (wl a))).
  { rewrite AD. cbn [den]. apply bv_eq. rewrite wbv_unsigned, AV, Z_to_bv_unsigned. symmetry. apply bv_wrap_small. rewrite bv_modulus_64. unfold two63, two64 in *. lia. }
  assert (RD : rdZ (bmem_of segs (ms_mem ms)) (to_Z (wl a)) (Z.to_nat (to_Z (msize_bytes SZ1))) = Some 0).
  { change (Z.to_nat (to_Z (msize_bytes SZ1))) with 1%nat. cbn [rdZ].
    rewrite (bmem_of_some segs (ms_mem ms) (to_Z (wl a)) (Z_to_bv 8 0) ltac:(unfold two63, two64 in *; lia)); [reflexivity|].
    unfold rb. rewrite BYTE. reflexivity. }
  assert (DV : den E (VL wzero) = ext_word sx 0 (to_Z (msize_bytes SZ1)) (Z_to_bv 64 0)).
  { cbn [den]. rewrite wbv_wzero. change (to_Z (msize_bytes SZ1)) with 1. symmetry. apply PkStep.ext_word_small; lia. }
  destruct (PkStepA.oracle_ILoad_mp segs OPS CHS LAWS MP HMPA E st ms model w i SZ1 sx rd rs off (to_Z (wl a)) 0 (VL wzero)
              HS HMP PCB FW EC DA OI HAD ltac:(unfold two63 in *; lia) ltac:(change (to_Z (msize_bytes SZ1)) with 1; unfold two63, two64 in *; lia) RD DV) as (ms' & mo' & STEP & MEM & ST2 & MP2).
  { intros j Hj. change (to_Z (msize_bytes SZ1)) with 1 in Hj. replace j with 0 by lia. rewrite Z.add_0_r. exact CH. }
  eexists _, ms', mo'. split; [reflexivity|]. auto.
Qed.

Theorem shloadlit_sound : forall pc, contract_sound segs OPS MP PB (shloadlit_c segs VIDS ZW pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [shloadlit_c c_apply] in HAP.
  destruct (shloadlit_sound_main E st ms model sts HS HMP HAP) as (st' & ms' & mo' & -> & STEP & MEM & HS' & HMP').
  apply (rz_astep segs ms model ms' mo' K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  apply (Hk st' (or_introl eq_refl) E ms' mo'); [| exact HMP'| exact HS'].
  split; [reflexivity|]. intros k Hk'. split; reflexivity.
Qed.
End Sound.
End ShLoadLit.
