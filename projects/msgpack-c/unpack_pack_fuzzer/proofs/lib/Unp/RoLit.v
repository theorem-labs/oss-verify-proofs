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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge GLib PkPeek PkStep PkStepA ShLoadLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import AccStep.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS CtrLib UB UG.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RoLit.
Section WithSegs.
Variable segs : list Segment.
Variable VIDS : list int.
Variable RV : int -> int -> option w64.

Definition rolit_apply (st : sstate) : option (list sstate) :=
  match PkPeek.load_at segs (s_pc st) with
  | Some (sz, sx, rd, rs, off) =>
      match sv_alu ALU_ADD (getr st rs) (VL off) with
      | VL a =>
          if negb (wt a) && negb (r5_eqb rd X0) && PrimInt63.ltb (s_pc st) bit62i
             && forallb (fun id => match find_op id (s_ops st) with Some _ => true | None => false end) VIDS
          then match RV (wl a) (msize_bytes sz) with
               | Some v => if wt v then None else
                           Some [setpc (setr st rd (sv_ext sx 0%uint63 (msize_bytes sz) (VL v))) (PrimInt63.add (s_pc st) 4%uint63)]
               | None => None
               end
          else None
      | _ => None
      end
  | _ => None
  end.
Definition rolit_c (pc : int) : contract := Contract pc rolit_apply.
End WithSegs.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable VIDS : list int.
Variable RV : int -> int -> option w64.
Variable CHS : list oinst -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis LAWS : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPS mo -> Forall (fun o => op_holds OPS (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CHS os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPS mo' /\
              Forall (fun o => op_holds OPS (fst o) (snd o) m mo') os.

Hypothesis HR : forall (os : list oinst) m mo a n v,
  (forall id, In id VIDS -> exists args, In (id, args) os /\ op_holds OPS id args m mo) -> RV a n = Some v -> wt v = false ->
  rdZ (bmem_of segs m) (to_Z a) (Z.to_nat (to_Z n)) = Some (to_Z (wl v)) /\
  (forall j, 0 <= j < to_Z n -> CHS os m mo (to_Z a + j)).
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma rolit_sound_main : forall E st ms model sts,
  st_ok segs OPS E st ms model -> MP model -> rolit_apply segs VIDS RV st = Some sts ->
  exists st' ms' mo', sts = [st'] /\ mi_account_step segs ms model = MachineOk (ms', mo') /\ ms_mem ms' = ms_mem ms /\
                      st_ok segs OPS E st' ms' mo' /\ MP mo'.
Proof.
  intros E st ms model sts HS HMP AP. unfold rolit_apply in AP.
  destruct (PkPeek.load_at segs (s_pc st)) as [[[[[sz sx] rd] rs] off]|] eqn:LA; [|discriminate].
  destruct (sv_alu ALU_ADD (getr st rs) (VL off)) as [a| | | | | | | | | |] eqn:AD; try discriminate.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:C; [|discriminate] end.
  destruct (RV (wl a) (msize_bytes sz)) as [v|] eqn:RVE; [|discriminate].
  destruct (wt v) eqn:WTV; [discriminate|]. injection AP as <-.
  apply andb_prop in C as [C FO]. apply andb_prop in C as [C PCB]. apply andb_prop in C as [WT RDX].
  apply negb_true_iff in WT.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (PRES : forall id, In id VIDS -> exists args, In (id, args) (insts E (s_ops st)) /\ op_holds OPS id args (ms_mem ms) model).
  { intros id Hid. pose proof (proj1 (forallb_forall _ _) FO id Hid) as F1. cbn beta in F1.
    destruct (find_op id (s_ops st)) as [zargs|] eqn:FZ; [|discriminate F1].
    destruct (ShLoadLit.find_op_in id (s_ops st) zargs FZ) as (o & OIN & OID & OARGS).
    exists (map (den E) (op_args o)). split.
    - unfold insts. apply in_map_iff. exists o. split; [rewrite OID; reflexivity| exact OIN].
    - pose proof (ops_hold_in OPS _ _ _ _ o Pops OIN) as OH. rewrite OID in OH. exact OH. }
  destruct (PkPeek.load_at_spec segs (s_pc st) _ _ _ _ _ LA) as (w & i & FW & EC & DA & OI). rewrite <- Ppc in FW.
  destruct (HR (insts E (s_ops st)) (ms_mem ms) model (wl a) (msize_bytes sz) v PRES RVE WTV) as [RD CH].
  assert (AV : w2Z a = to_Z (wl a)) by (unfold w2Z; rewrite WT; reflexivity).
  pose proof (to_Z_bounded (wl a)) as RA. rewrite wB_two63 in RA.
  assert (W8 : 1 <= to_Z (msize_bytes sz) <= 8) by (destruct sz; cbn [msize_bytes]; [change (to_Z 1%uint63) with 1| change (to_Z 2%uint63) with 2| change (to_Z 4%uint63) with 4| change (to_Z 8%uint63) with 8]; lia).
  assert (HAD : den E (sv_alu ALU_ADD (getr st rs) (VL off)) = Z_to_bv 64 (to_Z (wl a))).
  { rewrite AD. cbn [den]. apply bv_eq. rewrite wbv_unsigned, AV, Z_to_bv_unsigned. symmetry. apply bv_wrap_small. rewrite bv_modulus_64. unfold two63, two64 in *. lia. }
  assert (DV : den E (sv_ext sx 0%uint63 (msize_bytes sz) (VL v)) = ext_word sx 0 (to_Z (msize_bytes sz)) (Z_to_bv 64 (to_Z (wl v)))).
  { rewrite den_sv_ext.
    - change (to_Z 0%uint63) with 0. f_equal. cbn [den]. apply bv_eq. rewrite wbv_unsigned, Z_to_bv_unsigned. unfold w2Z. rewrite WTV.
      pose proof (to_Z_bounded (wl v)) as RB. rewrite wB_two63 in RB. symmetry. apply bv_wrap_small. rewrite bv_modulus_64. unfold two63, two64 in *. lia.
    - unfold width_ok. change (to_Z 0%uint63) with 0. lia. }
  destruct (PkStepA.oracle_ILoad_mp segs OPS CHS LAWS MP HMPA E st ms model w i sz sx rd rs off (to_Z (wl a)) (to_Z (wl v)) (sv_ext sx 0%uint63 (msize_bytes sz) (VL v))
              HS HMP PCB FW EC DA OI HAD ltac:(unfold two63 in *; lia) ltac:(unfold two63, two64 in *; lia) RD DV) as (ms' & mo' & STEP & MEM & ST2 & MP2).
  { intros j Hj. exact (CH j Hj). }
  eexists _, ms', mo'. split; [reflexivity|]. auto.
Qed.

Theorem rolit_sound : forall pc, contract_sound segs OPS MP PB (rolit_c segs VIDS RV pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [rolit_c c_apply] in HAP.
  destruct (rolit_sound_main E st ms model sts HS HMP HAP) as (st' & ms' & mo' & -> & STEP & MEM & HS' & HMP').
  apply (rz_astep segs ms model ms' mo' K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  apply (Hk st' (or_introl eq_refl) E ms' mo'); [| exact HMP'| exact HS'].
  split; [reflexivity|]. intros k Hk'. split; reflexivity.
Qed.
End Sound.
End RoLit.
