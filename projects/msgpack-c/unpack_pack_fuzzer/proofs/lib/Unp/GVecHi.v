(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound KnownT EntM.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GVecHi.

Definition vec_hi (n : int) (oA : w64) (k : int) : sv := VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k wzero)) (VL (wlit 3%uint63)).
Definition parse_vec_hi (h : sv) (k : int) : option (int * w64) :=
  match h with
  | VAlu ALU_SRL (VAlu ALU_SUB (VP n oA) (VP k' z)) (VL c) =>
      if PrimInt63.eqb k' k && weqb z wzero && weqb c (wlit 3%uint63) then Some (n, oA) else None
  | _ => None
  end.

Definition lit_mid (h : sv) : option w64 :=
  match h with
  | VL g => if negb (wt g) && PrimInt63.ltb (wl g) 288230376151711744%uint63   then Some (wlit (PrimInt63.lsl (wl g) 3%uint63)) else None
  | _ => None
  end.
Lemma lit_mid_den : forall E h k o, lit_mid h = Some o ->
  den E h = alu64 ALU_SRL (alu64 ALU_SUB (den E (VP k o)) (den E (VP k wzero))) (den E (VL (wlit 3%uint63))).
Proof.
  intros E h k o H. unfold lit_mid in H. destruct h as [g| | | | | | | | | |]; try discriminate.
  destruct (negb (wt g) && PrimInt63.ltb (wl g) 288230376151711744%uint63) eqn:Q; [|discriminate]. injection H as <-.
  apply andb_prop in Q as [T L]. apply negb_true_iff in T. apply Uint63.ltb_spec in L. change (to_Z 288230376151711744%uint63) with (2 ^ 58) in L.
  pose proof (int_range (wl g)) as RG.
  assert (SH : to_Z (PrimInt63.lsl (wl g) 3%uint63) = 8 * to_Z (wl g)).
  { rewrite Uint63.lsl_spec. change (to_Z 3%uint63) with 3. change (2 ^ 3) with 8. change wB with (2 ^ 63). rewrite Z.mod_small by lia. lia. }
  apply bv_eq. cbn [den alu64 alu]. rewrite bv_shiftr_unsigned, shamt6_bv. change (to_Z (shamt6 (wlit 3%uint63))) with 3.
  rewrite bv_sub_unsigned, !bv_add_unsigned, !wbv_unsigned, wzero_ok, wlit_ok, SH. unfold w2Z. rewrite T. cbn [Z.add].
  pose proof (bv_unsigned_in_range _ (ev E k)) as RK. rewrite bv_modulus_64, two64_eq in RK.
  unfold bv_wrap. rewrite bv_modulus_64, two64_eq. rewrite Z.add_0_r, (Z.mod_small (bv_unsigned (ev E k))) by lia.
  rewrite Zminus_mod_idemp_l. replace (bv_unsigned (ev E k) + 8 * to_Z (wl g) - bv_unsigned (ev E k)) with (8 * to_Z (wl g)) by lia.
  rewrite (Z.mod_small (8 * to_Z (wl g))) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.
Lemma parse_vec_hi_eq : forall h k n oA, parse_vec_hi h k = Some (n, oA) -> h = vec_hi n oA k.
Proof.
  intros h k n oA H. unfold parse_vec_hi in H.
  destruct h as [| |op a c| | | | | | | |]; try discriminate. destruct op; try discriminate.
  destruct a as [| |op2 p q| | | | | | | |]; try discriminate. destruct op2; try discriminate.
  destruct p as [|n0 o0| | | | | | | | |]; try discriminate. destruct q as [|k' z| | | | | | | | |]; try discriminate.
  destruct c as [c| | | | | | | | | |]; try discriminate.
  destruct (PrimInt63.eqb k' k && weqb z wzero && weqb c (wlit 3%uint63)) eqn:Q; [|discriminate]. injection H as -> ->.
  apply andb_prop in Q as [Q C3]. apply andb_prop in Q as [K Z0].
  apply Uint63.eqb_correct in K. apply (proj1 (weqb_ok _ _)) in Z0. apply (proj1 (weqb_ok _ _)) in C3. subst. reflexivity.
Qed.

Definition cands : list w64 := [wlit 8%uint63; wlit 16%uint63; wzero; wlit 24%uint63].
Fixpoint pick (fs : list fact) (old : sv) (nT : int) (l : list w64) : option w64 :=
  match l with
  | [] => None
  | o :: l' => match KnownT.KnownT.decide_eq_tt fs old (VP nT o) with Some true => Some o | _ => pick fs old nT l' end
  end.
Lemma pick_sound : forall E fs old nT l o, facts_hold E fs -> pick fs old nT l = Some o -> den E old = den E (VP nT o).
Proof.
  intros E fs old nT l. induction l as [|o0 l IH]; intros o FH H; cbn [pick] in H; [discriminate|].
  destruct (KnownT.KnownT.decide_eq_tt fs old (VP nT o0)) as [[|]|] eqn:D; try exact (IH o FH H).
  injection H as <-. pose proof (KnownT.KnownT.decide_eq_tt_sound E fs FH _ _ _ D) as Q. exact (proj1 (eqb_iff _ _ true) Q).
Qed.

Definition og (g : option (list gapc)) (l : list fact) : list gapc := match g with Some G => G | None => gaps l end.
Fixpoint pick_c (t1 t2 t3 : list fact) (old : sv) (nT : int) (l : list w64) (g1 g2 g3 : option (list gapc)) {struct l} : option w64 :=
  match l with
  | [] => None
  | o :: l' =>
      let G1 := og g1 t1 in
      match EntM.EntM.decide_eq_m G1 t1 old (VP nT o) with
      | Some true => Some o
      | Some false => pick_c t1 t2 t3 old nT l' (Some G1) g2 g3
      | None =>
          let G2 := og g2 t2 in
          match EntM.EntM.decide_eq_m G2 t2 old (VP nT o) with
          | Some true => Some o
          | Some false => pick_c t1 t2 t3 old nT l' (Some G1) (Some G2) g3
          | None =>
              let G3 := og g3 t3 in
              match EntM.EntM.decide_eq_m G3 t3 old (VP nT o) with
              | Some true => Some o
              | _ => pick_c t1 t2 t3 old nT l' (Some G1) (Some G2) (Some G3)
              end
          end
      end
  end.
Definition pick4 (fs : list fact) (old : sv) (nT : int) (l : list w64) : option w64 :=
  let vs := sv_vs old [nT] in
  pick_c (rel_facts vs fs) (rel_facts (close_vs fs vs vs) fs) fs old nT l None None None.

Lemma og_ok : forall g l, (g = None \/ g = Some (gaps l)) -> og g l = gaps l.
Proof. intros g l [-> | ->]; reflexivity. Qed.
Lemma pick_c_eq : forall fs old nT l g1 g2 g3,
  let vs := sv_vs old [nT] in let t1 := rel_facts vs fs in let t2 := rel_facts (close_vs fs vs vs) fs in
  (g1 = None \/ g1 = Some (gaps t1)) -> (g2 = None \/ g2 = Some (gaps t2)) -> (g3 = None \/ g3 = Some (gaps fs)) ->
  pick_c t1 t2 fs old nT l g1 g2 g3 = pick fs old nT l.
Proof.
  intros fs old nT l. cbn zeta. induction l as [|o l IH]; intros g1 g2 g3 H1 H2 H3; cbn [pick_c pick]; [reflexivity|].
  assert (VS : sv_vs old (sv_vs (VP nT o) []) = sv_vs old [nT]) by reflexivity.
  unfold KnownT.KnownT.decide_eq_tt, KnownT.KnownT.tiers. rewrite VS.
  rewrite (og_ok g1 _ H1), EntM.EntM.decide_eq_m_eq.
  destruct (decide_eq (rel_facts (sv_vs old [nT]) fs) old (VP nT o)) as [[|]|].
  - reflexivity.
  - apply IH; [right; reflexivity| exact H2| exact H3].
  - rewrite (og_ok g2 _ H2), EntM.EntM.decide_eq_m_eq.
    destruct (decide_eq (rel_facts (close_vs fs (sv_vs old [nT]) (sv_vs old [nT])) fs) old (VP nT o)) as [[|]|].
    + reflexivity.
    + apply IH; [right; reflexivity| right; reflexivity| exact H3].
    + rewrite (og_ok g3 _ H3), EntM.EntM.decide_eq_m_eq.
      destruct (decide_eq fs old (VP nT o)) as [[|]|]; [reflexivity| |]; (apply IH; right; reflexivity).
Qed.
Lemma pick4_eq : forall fs old nT l, pick4 fs old nT l = pick fs old nT l.
Proof. intros. unfold pick4. apply pick_c_eq; left; reflexivity. Qed.

Definition new_hi (nT : int) (o' : w64) (kB : int) : sv :=
  let g := VL (wlit (PrimInt63.lsr (wl o') 3%uint63)) in
  if PrimInt63.eqb nT kB then match lit_mid g with Some o'' => if weqb o'' o' then g else vec_hi nT o' kB | None => vec_hi nT o' kB end
  else vec_hi nT o' kB.
Lemma new_hi_den : forall E nT o' kB,
  den E (new_hi nT o' kB) = alu64 ALU_SRL (alu64 ALU_SUB (den E (VP nT o')) (den E (VP kB wzero))) (den E (VL (wlit 3%uint63))).
Proof.
  intros E nT o' kB. unfold new_hi.
  destruct (PrimInt63.eqb nT kB) eqn:EK; [| reflexivity]. apply Uint63.eqb_correct in EK. subst nT.
  destruct (lit_mid (VL (wlit (PrimInt63.lsr (wl o') 3%uint63)))) as [o''|] eqn:LM; [| reflexivity].
  destruct (weqb o'' o') eqn:WE; [| reflexivity]. apply (proj1 (weqb_ok _ _)) in WE. subst o''.
  exact (lit_mid_den E _ kB o' LM).
Qed.

Section WithPc.
Variable S_PC : int.
Variable S : w64.
Variable IB IE : nat.

Definition gvechi_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (_, _, _, ca) =>
      match nth_error ca IB, nth_error ca IE with
      | Some (VP kB _), Some (VP nT _) =>
          match find_link (s_facts st) kB S with
          | Some sh =>
              match IMap.find sh (s_regs st) with
              | Some r =>
                  match (match parse_vec_hi (rg_hi r) kB with Some x => Some x | None => match lit_mid (rg_hi r) with Some o => Some (kB, o) | None => None end end) with
                  | Some (n', oA) =>
                      if PrimInt63.eqb n' nT || PrimInt63.eqb sh 0%uint63 then None else
                      match pick4 (s_facts st) (VP n' oA) nT cands with
                      | Some o' => Some [setregs st (IMap.add sh (Region (rg_lo r) (new_hi nT o' kB) (rg_w r) (rg_bg r) (rg_cells r)) (s_regs st))]
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | _, _ => None
      end
  | None => None
  end.

Definition gvechi_contract : contract := Contract S_PC gvechi_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Theorem gvechi_sound : contract_sound segs OPS MP PB gvechi_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [gvechi_contract c_apply] in HAP. unfold gvechi_apply in HAP.
  destruct (the_op st) as [[[[md aw] ws] ca]|]; [|discriminate].
  destruct (nth_error ca IB) as [[|kB ob| | | | | | | | |]|]; try discriminate.
  destruct (nth_error ca IE) as [[|nT oe| | | | | | | | |]|]; try discriminate.
  destruct (find_link (s_facts st) kB S) as [sh|]; [|discriminate].
  destruct (IMap.find sh (s_regs st)) as [r|] eqn:F; [|discriminate].
  assert (HI : forall n' oA, (match parse_vec_hi (rg_hi r) kB with Some x => Some x | None => match lit_mid (rg_hi r) with Some o => Some (kB, o) | None => None end end) = Some (n', oA) ->
               den E (rg_hi r) = alu64 ALU_SRL (alu64 ALU_SUB (den E (VP n' oA)) (den E (VP kB wzero))) (den E (VL (wlit 3%uint63)))).
  { intros n' oA H. destruct (parse_vec_hi (rg_hi r) kB) as [[n0 o0]|] eqn:PH.
    - injection H as -> ->. rewrite (parse_vec_hi_eq _ _ _ _ PH). reflexivity.
    - destruct (lit_mid (rg_hi r)) as [o|] eqn:LM; [|discriminate]. injection H as <- <-. exact (lit_mid_den E _ kB o LM). }
  destruct (match parse_vec_hi (rg_hi r) kB with Some x => Some x | None => match lit_mid (rg_hi r) with Some o => Some (kB, o) | None => None end end) as [[n' oA]|] eqn:PH; [|discriminate].
  destruct (PrimInt63.eqb n' nT || PrimInt63.eqb sh 0%uint63) eqn:Q; [discriminate|].
  rewrite pick4_eq in HAP.
  destruct (pick (s_facts st) (VP n' oA) nT cands) as [o'|] eqn:PK; [|discriminate]. injection HAP as <-.
  apply orb_false_iff in Q as [_ SH0].
  refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl _ _) HMP _).
  apply (sethi_sound segs OPS E st ms model sh r (new_hi nT o' kB) HS F SH0).
  rewrite (HI n' oA eq_refl), new_hi_den.
  pose proof (pick_sound E (s_facts st) (VP n' oA) nT cands o' (so_facts _ _ _ _ _ _ HS) PK) as EQ.
  rewrite EQ. reflexivity.
Qed.

End Sound.
End WithPc.
End GVecHi.
