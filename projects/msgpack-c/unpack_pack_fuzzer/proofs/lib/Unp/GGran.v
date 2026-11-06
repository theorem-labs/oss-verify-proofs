(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound CaseF.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GGran.

Definition w3 : w64 := wlit 3%uint63.
Definition w7 : w64 := wlit 7%uint63.
Definition B63 : w64 := {| wt := true; wl := 0%uint63 |}.
Definition B60 : w64 := wlit 1152921504606846976%uint63.

Definition gran_src (o : sv) : option sv :=
  match o with
  | VAlu ALU_SRL X (VL s) => if weqb s w3 then Some X else None
  | VL c => if wltu c B60 then Some (VL (walu ALU_SLL c w3)) else None
  | _ => None
  end.

Definition gran_len (hi : sv) : option sv :=
  match hi with
  | VAlu ALU_SRL (VAlu ALU_ADD n (VL c)) (VL s) => if weqb c w7 && weqb s w3 then Some n else None
  | _ => None
  end.

Section WithPc.
Variable G_PC : int.
Variable RS : r5.
Variable OFF : w64.

Definition ggran_apply (st : sstate) : option (list sstate) :=
  let fs := s_facts st in
  match CaseF.twin_sel RS OFF st with
  | Some (o, hi) =>
      match gran_src o, gran_len hi with
      | Some X, Some n =>
          if match decide_ltu fs X n with Some true => true | _ => false end && wltu (snd (sv_bounds fs n)) B63
          then Some [addfact st (FULt o hi)] else None
      | _, _ => None
      end
  | None => None
  end.

Definition ggran_contract : contract := Contract G_PC ggran_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma sh3 : bv_unsigned (bv_and (wbv w3) (Z_to_bv 64 63)) = 3.
Proof. rewrite shamt6_bv. reflexivity. Qed.

Lemma srl3_unsigned : forall E (x : sv), bv_unsigned (den E (VAlu ALU_SRL x (VL w3))) = bv_unsigned (den E x) / 8.
Proof.
  intros E x. change (den E (VAlu ALU_SRL x (VL w3))) with (alu64 ALU_SRL (den E x) (den E (VL w3))).
  cbn [alu64 alu]. change (den E (VL w3)) with (wbv w3). rewrite bv_shiftr_unsigned, sh3, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma gran_src_spec : forall E o X, gran_src o = Some X -> bv_unsigned (den E o) = bv_unsigned (den E X) / 8.
Proof.
  intros E o X H. unfold gran_src in H.
  destruct o as [c| |op x y| | | | | | | |]; try discriminate H.
  - destruct (wltu c B60) eqn:LT; [|discriminate H]. injection H as <-.
    rewrite wltu_w2Z in LT. apply Z.ltb_lt in LT. change (w2Z B60) with (2 ^ 60) in LT.
    rewrite !den_VL. pose proof (w2Z_range c) as RC.
    assert (S8 : w2Z (walu ALU_SLL c w3) = 8 * w2Z c).
    { rewrite <- (wbv_unsigned (walu ALU_SLL c w3)), walu_ok. cbn [alu64 alu]. rewrite bv_shiftl_unsigned, sh3, Z.shiftl_mul_pow2 by lia.
      rewrite wbv_unsigned. change (2 ^ 3) with 8. unfold bv_wrap. rewrite bv_modulus_64. unfold two64. rewrite Z.mod_small by lia. lia. }
    change (wsll c w3) with (walu ALU_SLL c w3). rewrite S8. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
  - destruct op; try discriminate H. destruct y as [s| | | | | | | | | |]; try discriminate H.
    destruct (weqb s w3) eqn:E3; [|discriminate H]. injection H as <-. apply (proj1 (weqb_ok _ _)) in E3. subst s.
    apply srl3_unsigned.
Qed.

Lemma gran_len_spec : forall hi n, gran_len hi = Some n -> hi = VAlu ALU_SRL (VAlu ALU_ADD n (VL w7)) (VL w3).
Proof.
  intros hi n H. unfold gran_len in H.
  destruct hi as [| |op x y| | | | | | | |]; try discriminate H. destruct op; try discriminate H.
  destruct x as [| |op2 x1 x2| | | | | | | |]; try discriminate H. destruct op2; try discriminate H.
  destruct x2 as [c| | | | | | | | | |]; try discriminate H. destruct y as [s| | | | | | | | | |]; try discriminate H.
  destruct (weqb c w7) eqn:E7; [|discriminate H]. destruct (weqb s w3) eqn:E3; [|discriminate H]. cbn [andb] in H. injection H as <-.
  apply (proj1 (weqb_ok _ _)) in E7. apply (proj1 (weqb_ok _ _)) in E3. subst c s. reflexivity.
Qed.

Theorem ggran_sound : contract_sound segs OPS MP PB ggran_contract.
Proof.
  intros st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [ggran_contract c_apply] in HA. unfold ggran_apply in HA.
  destruct (CaseF.twin_sel RS OFF st) as [[o hi]|]; [|discriminate].
  destruct (gran_src o) as [X|] eqn:GS; [|discriminate]. destruct (gran_len hi) as [n|] eqn:GL; [|discriminate].
  destruct (decide_ltu (s_facts st) X n) as [[|]|] eqn:DL; try discriminate.
  destruct (wltu (snd (sv_bounds (s_facts st) n)) B63) eqn:HB; [|discriminate].
  cbn [andb] in HA. injection HA as <-.
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  pose proof (decide_ltu_sound E (s_facts st) FH X n true DL) as LT. apply (proj1 (ltu_iff _ _ true)) in LT.
  pose proof (sv_bounds_sound E (s_facts st) FH n) as I0. unfold inb in I0.
  rewrite wltu_w2Z in HB. apply Z.ltb_lt in HB. replace (w2Z B63) with (2 ^ 63) in HB by (vm_compute; reflexivity).
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP _).
  apply addfact_sound; [exact HS|]. cbn [fact_holds].
  rewrite (gran_src_spec E o X GS). apply gran_len_spec in GL. subst hi. rewrite srl3_unsigned.
  set (Xz := bv_unsigned (den E X)) in *. set (Nz := bv_unsigned (den E n)) in *.
  pose proof (bv_unsigned_in_range _ (den E X)) as RX. fold Xz in RX.
  assert (ADDu : bv_unsigned (den E (VAlu ALU_ADD n (VL w7))) = Nz + 7).
  { change (den E (VAlu ALU_ADD n (VL w7))) with (alu64 ALU_ADD (den E n) (den E (VL w7))). cbn [alu64 alu].
    rewrite bv_add_unsigned, den_VL. fold Nz. change (w2Z w7) with 7. unfold bv_wrap. rewrite bv_modulus_64. unfold two64. apply Z.mod_small. lia. }
  rewrite ADDu.
  replace (Nz + 7) with ((Nz - 1) + 1 * 8) by lia. rewrite Z.div_add by lia.
  assert (Xz / 8 <= (Nz - 1) / 8) by (apply Z.div_le_mono; lia). lia.
Qed.

End Sound.
End WithPc.
End GGran.
