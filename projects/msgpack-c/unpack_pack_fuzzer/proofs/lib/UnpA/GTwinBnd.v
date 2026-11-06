(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr CallA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP PlanS UG.
Open Scope Z_scope.

Module GTwinBnd.

Definition K_TWINw : w64 := wlit 9%uint63.

Definition is_lit (v : sv) : bool := match v with VL _ => true | _ => false end.

Definition win_fact (fs : list fact) (R : IMap.t region) (w : sv * sv * sv) : option fact :=
  match w with
  | (VP sh z, len, VL kd) =>
      if weqb z wzero && weqb kd K_TWINw && negb (PrimInt63.eqb sh 0%uint63) then
        match IMap.find sh R with
        | Some r =>
            let h := rg_hi r in
            if negb (is_lit h) && negb (has_fact (FULe h len) fs) && ActrA.vec_hi_in fs h len
            then Some (FULe h len) else None
        | None => None
        end
      else None
  | _ => None
  end.

Fixpoint win_facts (fs : list fact) (R : IMap.t region) (ws : list (sv * sv * sv)) : list fact :=
  match ws with
  | [] => []
  | w :: ws' => match win_fact fs R w with Some f => f :: win_facts fs R ws' | None => win_facts fs R ws' end
  end.

Fixpoint addfacts (st : sstate) (l : list fact) : sstate :=
  match l with [] => st | f :: l' => addfacts (addfact st f) l' end.

Section WithPc.
Variable B_PC : int.

Definition gtwinbnd_apply (st : sstate) : option (list sstate) :=
  match UG.the_op st with
  | Some (_, _, ws, _) =>
      match win_facts (s_facts st) (s_regs st) ws with
      | [] => None
      | l => Some [addfacts st l]
      end
  | None => None
  end.

Definition gtwinbnd_contract : contract := Contract B_PC gtwinbnd_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma win_fact_holds : forall E fs R w f, Forall (fact_holds E) fs -> win_fact fs R w = Some f -> fact_holds E f.
Proof.
  intros E fs R w f HF H. unfold win_fact in H.
  destruct w as [[lo len] kdv]. destruct lo as [|sh z| | | | | | | | |]; try discriminate H.
  destruct kdv as [kd| | | | | | | | | |]; try discriminate H.
  destruct (weqb z wzero && weqb kd K_TWINw && negb (PrimInt63.eqb sh 0%uint63)); [|discriminate H].
  destruct (IMap.find sh R) as [r|]; [|discriminate H].
  destruct (negb (is_lit (rg_hi r)) && negb (has_fact (FULe (rg_hi r) len) fs) && ActrA.vec_hi_in fs (rg_hi r) len) eqn:C; [|discriminate H].
  injection H as <-. apply andb_prop in C as [_ VH].
  cbn [fact_holds]. exact (CallA.vec_hi_in_sound E fs (rg_hi r) len HF VH).
Qed.

Lemma win_facts_hold : forall E fs R ws, Forall (fact_holds E) fs -> Forall (fact_holds E) (win_facts fs R ws).
Proof.
  intros E fs R ws HF. induction ws as [|w ws IH]; cbn [win_facts]; [constructor|].
  destruct (win_fact fs R w) as [f|] eqn:W; [|exact IH].
  constructor; [exact (win_fact_holds E fs R w f HF W) | exact IH].
Qed.

Lemma addfacts_sound : forall E l st ms model,
  st_ok segs OPS E st ms model -> Forall (fact_holds E) l -> st_ok segs OPS E (addfacts st l) ms model.
Proof.
  intros E l. induction l as [|f l IH]; intros st ms model HS HL; cbn [addfacts]; [exact HS|].
  inversion HL as [|? ? Hf HL']; subst. apply IH; [| exact HL']. exact (addfact_sound segs OPS E st ms model f HS Hf).
Qed.

Lemma addfacts_pc : forall l st, s_pc (addfacts st l) = s_pc st.
Proof. induction l as [|f l IH]; intros st; cbn [addfacts]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Theorem gtwinbnd_sound : contract_sound segs OPS MP PB gtwinbnd_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [gtwinbnd_contract c_apply] in HAP. unfold gtwinbnd_apply in HAP.
  destruct (UG.the_op st) as [[[[md aw] ws] ca]|]; [|discriminate].
  destruct (win_facts (s_facts st) (s_regs st) ws) as [|f0 l0] eqn:WF; [discriminate|]. injection HAP as <-.
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl _ _) HMP _).
  change (addfacts (addfact st f0) l0) with (addfacts st (f0 :: l0)).
  apply addfacts_sound; [exact HS|]. rewrite <- WF. apply win_facts_hold.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv]. exact Pfacts.
Qed.

End Sound.
End WithPc.
End GTwinBnd.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib.
Import Actr.TwinB CallA.TwinB.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP PlanS UG.
Open Scope Z_scope.

Module GTwinBnd.

Definition K_TWINw : w64 := wlit 9%uint63.

Definition is_lit (v : sv) : bool := match v with VL _ => true | _ => false end.

Definition win_fact (fs : list fact) (R : IMap.t region) (w : sv * sv * sv) : option fact :=
  match w with
  | (VP sh z, len, VL kd) =>
      if weqb z wzero && weqb kd K_TWINw && negb (PrimInt63.eqb sh 0%uint63) then
        match IMap.find sh R with
        | Some r =>
            let h := rg_hi r in
            if negb (is_lit h) && negb (has_fact (FULe h len) fs) && ActrA.vec_hi_in fs h len
            then Some (FULe h len) else None
        | None => None
        end
      else None
  | _ => None
  end.

Fixpoint win_facts (fs : list fact) (R : IMap.t region) (ws : list (sv * sv * sv)) : list fact :=
  match ws with
  | [] => []
  | w :: ws' => match win_fact fs R w with Some f => f :: win_facts fs R ws' | None => win_facts fs R ws' end
  end.

Fixpoint addfacts (st : sstate) (l : list fact) : sstate :=
  match l with [] => st | f :: l' => addfacts (addfact st f) l' end.

Section WithPc.
Variable B_PC : int.

Definition gtwinbnd_apply (st : sstate) : option (list sstate) :=
  match UG.the_op st with
  | Some (_, _, ws, _) =>
      match win_facts (s_facts st) (s_regs st) ws with
      | [] => None
      | l => Some [addfacts st l]
      end
  | None => None
  end.

Definition gtwinbnd_contract : contract := Contract B_PC gtwinbnd_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma win_fact_holds : forall E fs R w f, Forall (fact_holds E) fs -> win_fact fs R w = Some f -> fact_holds E f.
Proof.
  intros E fs R w f HF H. unfold win_fact in H.
  destruct w as [[lo len] kdv]. destruct lo as [|sh z| | | | | | | | |]; try discriminate H.
  destruct kdv as [kd| | | | | | | | | |]; try discriminate H.
  destruct (weqb z wzero && weqb kd K_TWINw && negb (PrimInt63.eqb sh 0%uint63)); [|discriminate H].
  destruct (IMap.find sh R) as [r|]; [|discriminate H].
  destruct (negb (is_lit (rg_hi r)) && negb (has_fact (FULe (rg_hi r) len) fs) && ActrA.vec_hi_in fs (rg_hi r) len) eqn:C; [|discriminate H].
  injection H as <-. apply andb_prop in C as [_ VH].
  cbn [fact_holds]. exact (CallA.TwinB.vec_hi_in_sound E fs (rg_hi r) len HF VH).
Qed.

Lemma win_facts_hold : forall E fs R ws, Forall (fact_holds E) fs -> Forall (fact_holds E) (win_facts fs R ws).
Proof.
  intros E fs R ws HF. induction ws as [|w ws IH]; cbn [win_facts]; [constructor|].
  destruct (win_fact fs R w) as [f|] eqn:W; [|exact IH].
  constructor; [exact (win_fact_holds E fs R w f HF W) | exact IH].
Qed.

Lemma addfacts_sound : forall E l st ms model,
  st_ok segs OPS E st ms model -> Forall (fact_holds E) l -> st_ok segs OPS E (addfacts st l) ms model.
Proof.
  intros E l. induction l as [|f l IH]; intros st ms model HS HL; cbn [addfacts]; [exact HS|].
  inversion HL as [|? ? Hf HL']; subst. apply IH; [| exact HL']. exact (addfact_sound segs OPS E st ms model f HS Hf).
Qed.

Lemma addfacts_pc : forall l st, s_pc (addfacts st l) = s_pc st.
Proof. induction l as [|f l IH]; intros st; cbn [addfacts]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Theorem gtwinbnd_sound : contract_sound segs OPS MP PB gtwinbnd_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [gtwinbnd_contract c_apply] in HAP. unfold gtwinbnd_apply in HAP.
  destruct (UG.the_op st) as [[[[md aw] ws] ca]|]; [|discriminate].
  destruct (win_facts (s_facts st) (s_regs st) ws) as [|f0 l0] eqn:WF; [discriminate|]. injection HAP as <-.
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl _ _) HMP _).
  change (addfacts (addfact st f0) l0) with (addfacts st (f0 :: l0)).
  apply addfacts_sound; [exact HS|]. rewrite <- WF. apply win_facts_hold.
  destruct HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv]. exact Pfacts.
Qed.

End Sound.
End WithPc.
End GTwinBnd.
End TwinB.
