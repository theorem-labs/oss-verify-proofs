(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree PkOps PkLib GLib PkStack PkPeek CapLen.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS HeapOp UB UG TR PK PKL PkStack.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkMid.

Definition w3 : w64 := wlit 3%uint63.
Definition w5 : w64 := wlit 5%uint63.
Definition INV3 : w64 := {| wt := true; wl := 3074457345618258603%uint63 |}.

Definition cnt_of (x : sv) : option (sv * sv) :=
  match x with
  | VMd M_MUL (VAlu ALU_SRA (VAlu ALU_SUB e b) (VL s)) (VL c) => if weqb s w3 && weqb c INV3 then Some (e, b) else None
  | _ => None
  end.

Definition W24 : w64 := wlit 24%uint63.
Fixpoint find_vd (fs : list fact) (j : int) : option (sv * sv) :=
  match fs with
  | [] => None
  | FEq e (VAlu ALU_ADD b (VMd M_MUL (VP j' o') (VL s))) :: fs' =>
      if PrimInt63.eqb j' j && weqb o' wzero && weqb s W24 then Some (e, b) else find_vd fs' j
  | _ :: fs' => find_vd fs' j
  end.
Definition cnt_of_f (fs : list fact) (x : sv) : option (sv * sv) :=
  match x with
  | VMd M_MUL (VAlu ALU_SRA (VMd M_MUL (VP j o) (VL s24)) (VL s)) (VL c) =>
      if weqb o wzero && weqb s24 W24 && weqb s w3 && weqb c INV3 && existsb (fact_eqb (FULe (VP j wzero) (VL CapLen.VD_MAX))) fs
      then find_vd fs j else None
  | _ => None
  end.
Definition cnt_of2 (fs : list fact) (x : sv) : option (sv * sv) :=
  match cnt_of x with Some r => Some r | None => cnt_of_f fs x end.

Definition mid_of (fs : list fact) (v : sv) : option (sv * sv * sv) :=
  match v with
  | VAlu ALU_ADD b0 (VAlu ALU_SUB (VAlu ALU_SLL x (VL s5)) (VAlu ALU_SLL x' (VL s3))) =>
      if weqb s5 w5 && weqb s3 w3 && sv_eqb x x' then
        match cnt_of2 fs x with Some (e, b) => Some (b0, e, b) | None => None end
      else None
  | _ => None
  end.

Definition same (fs : list fact) (a b : sv) : bool :=
  if sv_eqb a b then true else PkPeek.dec_true (decide_eq fs a b).

Definition has_vd (fs : list fact) (b e : sv) : bool :=
  existsb (fun f => match f with
                    | FEq e' (VAlu ALU_ADD b' (VMd M_MUL (VP j o) (VL s))) =>
                        sv_eqb e' e && sv_eqb b' b && weqb o wzero && weqb s W24
                        && existsb (fact_eqb (FULe (VP j wzero) (VL CapLen.VD_MAX))) fs
                    | _ => false
                    end) fs
  && existsb (fact_eqb (FULe b e)) fs.

Definition ghost_ok (st : sstate) (b e : sv) : bool :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 3%uint63 then
        match parse_ca ca with
        | Some c => same (s_facts st) b (c_eb c) && same (s_facts st) e (c_ee c)
        | None => false
        end
      else false
  | None => false
  end.

Section WithPc.
Variable M_PC : int.
Variable R : r5.

Definition mid_val (fs : list fact) (b0 e b : sv) : sv :=
  if same fs b0 b then e else sv_alu ALU_ADD b0 (sv_alu ALU_SUB e b).

Definition pkmid_apply (st : sstate) : option (list sstate) :=
  match mid_of (s_facts st) (getr st R) with
  | Some (b0, e, b) =>
      let fs := s_facts st in
      if negb (r5_eqb R X0) then
        if same fs e b then Some [setr st R b0]
        else if (if ghost_ok st b e then true else has_vd fs b e) then Some [setr st R (mid_val fs b0 e b)]
        else None
      else None
  | None => None
  end.

Definition pkmid_contract : contract := Contract M_PC pkmid_apply.

End WithPc.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma cnt_of_spec : forall x e b, cnt_of x = Some (e, b) -> x = VMd M_MUL (VAlu ALU_SRA (VAlu ALU_SUB e b) (VL w3)) (VL INV3).
Proof.
  intros x e b H. unfold cnt_of in H.
  destruct x as [| | | |mo y1 y2| | | | | |]; try discriminate H. destruct mo; try discriminate H.
  destruct y1 as [| |o2 z1 z2| | | | | | | |]; try discriminate H. destruct o2; try discriminate H.
  destruct z1 as [| |o3 u1 u2| | | | | | | |]; try discriminate H. destruct o3; try discriminate H.
  destruct z2 as [s| | | | | | | | | |]; try discriminate H.
  destruct y2 as [c| | | | | | | | | |]; try discriminate H.
  destruct (weqb s w3) eqn:E1; [|discriminate H]. destruct (weqb c INV3) eqn:E2; [|discriminate H].
  cbn [andb] in H. injection H as <- <-.
  apply (proj1 (weqb_ok _ _)) in E1. apply (proj1 (weqb_ok _ _)) in E2. subst s c. reflexivity.
Qed.

Lemma mid_of_spec : forall fs v b0 e b, mid_of fs v = Some (b0, e, b) ->
  exists x, cnt_of2 fs x = Some (e, b) /\ v = VAlu ALU_ADD b0 (VAlu ALU_SUB (VAlu ALU_SLL x (VL w5)) (VAlu ALU_SLL x (VL w3))).
Proof.
  intros fs v b0 e b H. unfold mid_of in H.
  destruct v as [| |o1 a1 a2| | | | | | | |]; try discriminate H. destruct o1; try discriminate H.
  destruct a2 as [| |o2 y1 y2| | | | | | | |]; try discriminate H. destruct o2; try discriminate H.
  destruct y1 as [| |o3 x s5v| | | | | | | |]; try discriminate H. destruct o3; try discriminate H.
  destruct s5v as [s5| | | | | | | | | |]; try discriminate H.
  destruct y2 as [| |o4 x' s3v| | | | | | | |]; try discriminate H. destruct o4; try discriminate H.
  destruct s3v as [s3| | | | | | | | | |]; try discriminate H.
  destruct (weqb s5 w5) eqn:E5; [|discriminate H]. destruct (weqb s3 w3) eqn:E3; [|discriminate H].
  destruct (sv_eqb x x') eqn:EX; [|discriminate H]. cbn [andb] in H.
  destruct (cnt_of2 fs x) as [[e1 b1]|] eqn:CO; [|discriminate H]. injection H as <- <- <-.
  apply sv_eqb_eq in EX. subst x'. apply (proj1 (weqb_ok _ _)) in E5. apply (proj1 (weqb_ok _ _)) in E3. subst s5 s3.
  exists x. split; [exact CO| reflexivity].
Qed.

Lemma cnt_word : forall (wb we : word) n, bv_unsigned we = bv_unsigned wb + 24 * n -> 0 <= n <= CapLen.VD_MAXZ ->
  bv_unsigned (mul_div M_MUL (alu64 ALU_SRA (alu64 ALU_SUB we wb) (wbv w3)) (wbv INV3)) = n.
Proof.
  intros wb we n EQ RN. unfold CapLen.VD_MAXZ in RN.
  pose proof (bv_unsigned_in_range _ wb) as RB. pose proof (bv_unsigned_in_range _ we) as RE. rewrite bv_modulus_64 in RB, RE. unfold two64 in RB, RE.
  assert (SUBu : bv_unsigned (alu64 ALU_SUB we wb) = 24 * n).
  { cbn [alu64 alu]. rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64. unfold two64. rewrite Z.mod_small by lia. lia. }
  assert (SH3 : bv_unsigned (bv_and (wbv w3) (Z_to_bv 64 63)) = 3) by (rewrite shamt6_bv; reflexivity).
  assert (SRAu : bv_unsigned (alu64 ALU_SRA (alu64 ALU_SUB we wb) (wbv w3)) = 3 * n).
  { cbn [alu64 alu]. cbn [alu64 alu] in SUBu. rewrite bv_ashiftr_unsigned, SH3.
    rewrite (bv_signed_small63 _) by (rewrite SUBu; unfold two63; lia).
    rewrite SUBu, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    replace (24 * n) with (3 * n * 8) by lia. rewrite Z.div_mul by lia.
    unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. unfold two64. lia. }
  unfold mul_div. rewrite bv_mul_unsigned, SRAu, wbv_unsigned.
  replace (w2Z INV3) with 12297829382473034411 by (vm_compute; reflexivity).
  unfold bv_wrap. rewrite bv_modulus_64. unfold two64.
  replace (3 * n * 12297829382473034411) with (n + (2 * n) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma cnt_word_j : forall (wj : word) j, bv_unsigned wj = j -> 0 <= j <= CapLen.VD_MAXZ ->
  bv_unsigned (mul_div M_MUL (alu64 ALU_SRA (mul_div M_MUL wj (wbv W24)) (wbv w3)) (wbv INV3)) = j.
Proof.
  intros wj j EJ RJ. unfold CapLen.VD_MAXZ in RJ.
  assert (M24 : bv_unsigned (mul_div M_MUL wj (wbv W24)) = 24 * j).
  { unfold mul_div. rewrite bv_mul_unsigned, EJ, wbv_unsigned. replace (w2Z W24) with 24 by (vm_compute; reflexivity).
    unfold bv_wrap. rewrite bv_modulus_64. unfold two64. rewrite Z.mod_small by lia. lia. }
  assert (SH3 : bv_unsigned (bv_and (wbv w3) (Z_to_bv 64 63)) = 3) by (rewrite shamt6_bv; reflexivity).
  assert (SRAu : bv_unsigned (alu64 ALU_SRA (mul_div M_MUL wj (wbv W24)) (wbv w3)) = 3 * j).
  { cbn [alu64 alu]. rewrite bv_ashiftr_unsigned, SH3.
    rewrite (bv_signed_small63 _) by (rewrite M24; unfold two63; lia).
    rewrite M24, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    replace (24 * j) with (3 * j * 8) by lia. rewrite Z.div_mul by lia.
    unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. unfold two64. lia. }
  unfold mul_div at 1. rewrite bv_mul_unsigned, SRAu, wbv_unsigned.
  replace (w2Z INV3) with 12297829382473034411 by (vm_compute; reflexivity).
  unfold bv_wrap. rewrite bv_modulus_64. unfold two64.
  replace (3 * j * 12297829382473034411) with (j + (2 * j) * 2 ^ 64) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma find_vd_spec : forall fs j e b, find_vd fs j = Some (e, b) -> In (FEq e (VAlu ALU_ADD b (VMd M_MUL (VP j wzero) (VL W24)))) fs.
Proof.
  induction fs as [|f fs IH]; intros j e b H; cbn [find_vd] in H; [discriminate|].
  destruct f as [| | | |p q| | |]; try (right; exact (IH _ _ _ H)).
  destruct q as [| |o1 b' m| | | | | | | |]; try (right; exact (IH _ _ _ H)). destruct o1; try (right; exact (IH _ _ _ H)).
  destruct m as [| | | |mo jv sv24| | | | | |]; try (right; exact (IH _ _ _ H)). destruct mo; try (right; exact (IH _ _ _ H)).
  destruct jv as [|j' o'| | | | | | | | |]; try (right; exact (IH _ _ _ H)). destruct sv24 as [s| | | | | | | | | |]; try (right; exact (IH _ _ _ H)).
  destruct (PrimInt63.eqb j' j && weqb o' wzero && weqb s W24) eqn:C; [| right; exact (IH _ _ _ H)].
  injection H as <- <-. apply andb_prop in C as [C Cs]. apply andb_prop in C as [Cj Co].
  apply Uint63.eqb_correct in Cj. apply weqb_eq in Co. apply weqb_eq in Cs. subst j' o' s. left. reflexivity.
Qed.
Lemma cnt_of2_val : forall E fs x e b n, facts_hold E fs -> cnt_of2 fs x = Some (e, b) ->
  bv_unsigned (den E e) = bv_unsigned (den E b) + 24 * n -> 0 <= n <= CapLen.VD_MAXZ ->
  bv_unsigned (den E x) = n.
Proof.
  intros E fs x e b n FH H GEO RN. unfold cnt_of2 in H.
  destruct (cnt_of x) as [[e1 b1]|] eqn:CO.
  - injection H as <- <-. rewrite (cnt_of_spec _ _ _ CO). cbn [den]. exact (cnt_word _ _ n GEO RN).
  - unfold cnt_of_f in H.
    destruct x as [| | | |mo y1 y2| | | | | |]; try discriminate H. destruct mo; try discriminate H.
    destruct y1 as [| |o2 z1 z2| | | | | | | |]; try discriminate H. destruct o2; try discriminate H.
    destruct z1 as [| | | |mo2 u1 u2| | | | | |]; try discriminate H. destruct mo2; try discriminate H.
    destruct u1 as [|j o| | | | | | | | |]; try discriminate H. destruct u2 as [s24| | | | | | | | | |]; try discriminate H.
    destruct z2 as [s| | | | | | | | | |]; try discriminate H. destruct y2 as [c| | | | | | | | | |]; try discriminate H.
    destruct (weqb o wzero && weqb s24 W24 && weqb s w3 && weqb c INV3 && existsb (fact_eqb (FULe (VP j wzero) (VL CapLen.VD_MAX))) fs) eqn:C; [|discriminate H].
    apply andb_prop in C as [C BJ]. apply andb_prop in C as [C Ec]. apply andb_prop in C as [C Es]. apply andb_prop in C as [Eo E24].
    apply weqb_eq in Eo. apply weqb_eq in E24. apply weqb_eq in Es. apply weqb_eq in Ec. subst o s24 s c.
    apply existsb_exists in BJ as (fb & HfB & QB). apply fact_eqb_eq in QB. subst fb.
    pose proof (find_vd_spec _ _ _ _ H) as HF.
    pose proof (proj1 (Forall_forall _ _) FH _ HF) as F1. pose proof (proj1 (Forall_forall _ _) FH _ HfB) as F2. cbn [fact_holds] in F1, F2.
    rewrite den_VL in F2. change (w2Z CapLen.VD_MAX) with CapLen.VD_MAXZ in F2. rewrite (den_VP0 E j wzero (weqb_refl _)) in F2.
    pose proof (bv_unsigned_in_range _ (den E b)) as RB. pose proof (bv_unsigned_in_range _ (den E e)) as RE. rewrite bv_modulus_64 in RB, RE. unfold two64 in RB, RE.
    pose proof (evk_range E j) as RJ. unfold CapLen.VD_MAXZ in F2, RN.

    assert (EJ : bv_unsigned (ev E j) = n).
    { assert (EE : bv_unsigned (den E e) = (bv_unsigned (den E b) + 24 * bv_unsigned (ev E j)) mod 2 ^ 64).
      { rewrite F1. cbn [den]. change (alu64 ALU_ADD ?x ?y) with (bv_add x y). unfold mul_div.
        rewrite bv_add_unsigned, bv_mul_unsigned, bv_add_unsigned, !wbv_unsigned.
        change (w2Z wzero) with 0. replace (w2Z W24) with 24 by (vm_compute; reflexivity).
        unfold bv_wrap. rewrite bv_modulus_64. unfold two64. rewrite Z.add_0_r, (Z.mod_small (bv_unsigned (ev E j))) by lia.
        rewrite (Z.mod_small (bv_unsigned (ev E j) * 24)) by lia. f_equal. lia. }
      rewrite GEO in EE.
      destruct (Z_lt_ge_dec (bv_unsigned (den E b) + 24 * bv_unsigned (ev E j)) (2 ^ 64)) as [Lt|Ge].
      - rewrite Z.mod_small in EE by lia. lia.
      - exfalso. assert (X : (bv_unsigned (den E b) + 24 * bv_unsigned (ev E j)) mod 2 ^ 64 = bv_unsigned (den E b) + 24 * bv_unsigned (ev E j) - 2 ^ 64).
        { symmetry. apply (Z.mod_unique _ _ 1); lia. }
        lia. }
    assert (EJ' : bv_unsigned (den E (VP j wzero)) = n) by (rewrite (den_VP0 E j wzero (weqb_refl _)); exact EJ).
    change (den E (VMd M_MUL (VAlu ALU_SRA (VMd M_MUL (VP j wzero) (VL W24)) (VL w3)) (VL INV3)))
      with (mul_div M_MUL (alu64 ALU_SRA (mul_div M_MUL (den E (VP j wzero)) (wbv W24)) (wbv w3)) (wbv INV3)).
    exact (cnt_word_j _ n EJ' ltac:(unfold CapLen.VD_MAXZ; lia)).
Qed.

Lemma same_sound : forall E fs a b, facts_hold E fs -> same fs a b = true -> den E a = den E b.
Proof.
  intros E fs a b FH H. unfold same in H. destruct (sv_eqb a b) eqn:EQ; [apply sv_eqb_eq in EQ; subst; reflexivity|].
  unfold PkPeek.dec_true in H. destruct (decide_eq fs a b) as [[|]|] eqn:D; try discriminate.
  pose proof (decide_eq_sound E fs FH a b true D) as Q. exact (proj1 (eqb_iff _ _ true) Q).
Qed.

Lemma mid24_word : forall (wb we : word) n, bv_unsigned we = bv_unsigned wb + 24 * n -> 0 <= n <= CapLen.VD_MAXZ ->
  let x := mul_div M_MUL (alu64 ALU_SRA (alu64 ALU_SUB we wb) (wbv w3)) (wbv INV3) in
  alu64 ALU_ADD wb (alu64 ALU_SUB (alu64 ALU_SLL x (wbv w5)) (alu64 ALU_SLL x (wbv w3))) = we.
Proof.
  intros wb we n EQ RN x. unfold CapLen.VD_MAXZ in RN.
  pose proof (bv_unsigned_in_range _ wb) as RB. pose proof (bv_unsigned_in_range _ we) as RE. rewrite bv_modulus_64 in RB, RE. unfold two64 in RB, RE.
  assert (SUBu : bv_unsigned (alu64 ALU_SUB we wb) = 24 * n).
  { cbn [alu64 alu]. rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64. unfold two64. rewrite Z.mod_small by lia. lia. }
  assert (SH3 : bv_unsigned (bv_and (wbv w3) (Z_to_bv 64 63)) = 3) by (rewrite shamt6_bv; reflexivity).
  assert (SH5 : bv_unsigned (bv_and (wbv w5) (Z_to_bv 64 63)) = 5) by (rewrite shamt6_bv; reflexivity).
  assert (SRAu : bv_unsigned (alu64 ALU_SRA (alu64 ALU_SUB we wb) (wbv w3)) = 3 * n).
  { cbn [alu64 alu]. cbn [alu64 alu] in SUBu. rewrite bv_ashiftr_unsigned, SH3.
    rewrite (bv_signed_small63 _) by (rewrite SUBu; unfold two63; lia).
    rewrite SUBu, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    replace (24 * n) with (3 * n * 8) by lia. rewrite Z.div_mul by lia.
    unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. unfold two64. lia. }
  assert (Xu : bv_unsigned x = n).
  { subst x. unfold mul_div. rewrite bv_mul_unsigned, SRAu, wbv_unsigned.
    replace (w2Z INV3) with 12297829382473034411 by (vm_compute; reflexivity).
    unfold bv_wrap. rewrite bv_modulus_64. unfold two64.
    replace (3 * n * 12297829382473034411) with (n + (2 * n) * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  apply bv_eq. cbn [alu64 alu].
  rewrite bv_add_unsigned, bv_sub_unsigned, !bv_shiftl_unsigned, SH3, SH5, Xu, !Z.shiftl_mul_pow2 by lia.
  change (2 ^ 5) with 32. change (2 ^ 3) with 8.
  unfold bv_wrap. rewrite bv_modulus_64. unfold two64.
  rewrite (Z.mod_small (n * 32)) by lia. rewrite (Z.mod_small (n * 8)) by lia.
  rewrite (Z.mod_small (n * 32 - n * 8)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mid24_word_gen : forall (wb0 wb we : word) n, bv_unsigned we = bv_unsigned wb + 24 * n -> 0 <= n <= CapLen.VD_MAXZ ->
  let x := mul_div M_MUL (alu64 ALU_SRA (alu64 ALU_SUB we wb) (wbv w3)) (wbv INV3) in
  alu64 ALU_ADD wb0 (alu64 ALU_SUB (alu64 ALU_SLL x (wbv w5)) (alu64 ALU_SLL x (wbv w3))) = alu64 ALU_ADD wb0 (alu64 ALU_SUB we wb).
Proof.
  intros wb0 wb we n EQ RN x. unfold CapLen.VD_MAXZ in RN.
  pose proof (bv_unsigned_in_range _ wb) as RB. pose proof (bv_unsigned_in_range _ we) as RE. rewrite bv_modulus_64 in RB, RE. unfold two64 in RB, RE.
  assert (SUBu : bv_unsigned (alu64 ALU_SUB we wb) = 24 * n).
  { cbn [alu64 alu]. rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64. unfold two64. rewrite Z.mod_small by lia. lia. }
  assert (SH3 : bv_unsigned (bv_and (wbv w3) (Z_to_bv 64 63)) = 3) by (rewrite shamt6_bv; reflexivity).
  assert (SH5 : bv_unsigned (bv_and (wbv w5) (Z_to_bv 64 63)) = 5) by (rewrite shamt6_bv; reflexivity).
  assert (SRAu : bv_unsigned (alu64 ALU_SRA (alu64 ALU_SUB we wb) (wbv w3)) = 3 * n).
  { cbn [alu64 alu]. cbn [alu64 alu] in SUBu. rewrite bv_ashiftr_unsigned, SH3.
    rewrite (bv_signed_small63 _) by (rewrite SUBu; unfold two63; lia).
    rewrite SUBu, Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    replace (24 * n) with (3 * n * 8) by lia. rewrite Z.div_mul by lia.
    unfold bv_wrap. rewrite bv_modulus_64. apply Z.mod_small. unfold two64. lia. }
  assert (Xu : bv_unsigned x = n).
  { subst x. unfold mul_div. rewrite bv_mul_unsigned, SRAu, wbv_unsigned.
    replace (w2Z INV3) with 12297829382473034411 by (vm_compute; reflexivity).
    unfold bv_wrap. rewrite bv_modulus_64. unfold two64.
    replace (3 * n * 12297829382473034411) with (n + (2 * n) * 2 ^ 64) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  cbn [alu64 alu]. f_equal. apply bv_eq. cbn [alu64 alu] in SUBu.
  rewrite bv_sub_unsigned, !bv_shiftl_unsigned, SH3, SH5, Xu, !Z.shiftl_mul_pow2, SUBu by lia.
  change (2 ^ 5) with 32. change (2 ^ 3) with 8.
  unfold bv_wrap. rewrite bv_modulus_64. unfold two64.
  rewrite (Z.mod_small (n * 32)) by lia. rewrite (Z.mod_small (n * 8)) by lia.
  rewrite (Z.mod_small (n * 32 - n * 8)) by lia. lia.
Qed.

Lemma ghost_ok_geom : forall E st ms model b e,
  st_ok segs OPS E st ms model -> ghost_ok st b e = true ->
  exists n, bv_unsigned (den E e) = bv_unsigned (den E b) + 24 * n /\ 0 <= n <= CapLen.VD_MAXZ.
Proof.
  intros E st ms model b e HS GO. unfold ghost_ok in GO.
  destruct (the_op st) as [[[[md aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb md 3%uint63) eqn:MD; [|discriminate].
  destruct (parse_ca ca) as [c|] eqn:PC; [|discriminate].
  apply andb_prop in GO as [S1 S2].
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  apply (same_sound E _ _ _ FH) in S1. apply (same_sound E _ _ _ FH) in S2. rewrite S1, S2. clear S1 S2.
  apply Uint63.eqb_correct in MD. subst md.
  pose proof (so_ops _ _ _ _ _ _ HS) as Pops.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate PC.
  cbn [parse_ca] in PC. injection PC as <-. cbn [c_ee c_eb].
  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (mdZ & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  apply CW3 in HC. unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
  destruct HC as (g & ls & L & P & O & Wk & M & GH & CO).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [a_eb a_ee] in Leb, Lee.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  exists (v_size (k_evec g)). split.
  - rewrite <- Lee, <- Leb. unfold v_end. rewrite EL. unfold ELEM_SIZE. reflexivity.
  - unfold CapLen.VD_MAXZ. destruct VE as [(_ & _ & E0)|[VV (CP & _ & C1024)]].
    + rewrite SZ, E0. cbn. lia.
    + destruct VV as (V1 & V2 & V3 & V4). lia.
Qed.

Lemma has_vd_geom : forall E fs b e, facts_hold E fs -> has_vd fs b e = true ->
  exists n, bv_unsigned (den E e) = bv_unsigned (den E b) + 24 * n /\ 0 <= n <= CapLen.VD_MAXZ.
Proof.
  intros E fs b e FH H. unfold has_vd in H. apply andb_prop in H as [H1 H3].
  apply existsb_exists in H1 as (f & Hf & Q). apply existsb_exists in H3 as (f3 & Hf3 & Q3).
  apply fact_eqb_eq in Q3. subst f3.
  destruct f as [| | | |e' r| | |]; try discriminate Q.
  destruct r as [| |o1 b' m| | | | | | | |]; try discriminate Q. destruct o1; try discriminate Q.
  destruct m as [| | | |mo jv sv24| | | | | |]; try discriminate Q. destruct mo; try discriminate Q.
  destruct jv as [|j o| | | | | | | | |]; try discriminate Q. destruct sv24 as [s| | | | | | | | | |]; try discriminate Q.
  apply andb_prop in Q as [Q Q2]. apply andb_prop in Q as [Q Qs]. apply andb_prop in Q as [Q Qo]. apply andb_prop in Q as [Qe Qb].
  apply sv_eqb_eq in Qe. apply sv_eqb_eq in Qb. subst e' b'. apply weqb_eq in Qo. apply weqb_eq in Qs. subst o s.
  apply existsb_exists in Q2 as (f2 & Hf2 & Q2). apply fact_eqb_eq in Q2. subst f2.
  pose proof (proj1 (Forall_forall _ _) FH _ Hf) as F1. pose proof (proj1 (Forall_forall _ _) FH _ Hf2) as F2.
  pose proof (proj1 (Forall_forall _ _) FH _ Hf3) as F3. cbn [fact_holds] in F1, F2, F3.
  rewrite den_VL in F2. change (w2Z CapLen.VD_MAX) with CapLen.VD_MAXZ in F2.
  rewrite (den_VP0 E j wzero (weqb_refl _)) in F2.
  exists (bv_unsigned (ev E j)). pose proof (evk_range E j) as RJ. split; [| lia].
  pose proof (bv_unsigned_in_range _ (den E b)) as RB. pose proof (bv_unsigned_in_range _ (den E e)) as RE. rewrite bv_modulus_64 in RB, RE. unfold two64 in RB, RE.
  unfold CapLen.VD_MAXZ in F2.
  assert (EE : bv_unsigned (den E e) = (bv_unsigned (den E b) + 24 * bv_unsigned (ev E j)) mod 2 ^ 64).
  { rewrite F1. cbn [den]. change (alu64 ALU_ADD ?x ?y) with (bv_add x y). unfold mul_div.
    rewrite bv_add_unsigned, bv_mul_unsigned, bv_add_unsigned, !wbv_unsigned.
    change (w2Z wzero) with 0. replace (w2Z W24) with 24 by (vm_compute; reflexivity).
    unfold bv_wrap. rewrite bv_modulus_64. unfold two64. rewrite Z.add_0_r, (Z.mod_small (bv_unsigned (ev E j))) by lia.
    rewrite (Z.mod_small (bv_unsigned (ev E j) * 24)) by lia. f_equal. lia. }
  destruct (Z_lt_ge_dec (bv_unsigned (den E b) + 24 * bv_unsigned (ev E j)) (2 ^ 64)) as [Lt|Ge].
  - rewrite Z.mod_small in EE by lia. exact EE.
  - exfalso. assert (X : (bv_unsigned (den E b) + 24 * bv_unsigned (ev E j)) mod 2 ^ 64 = bv_unsigned (den E b) + 24 * bv_unsigned (ev E j) - 2 ^ 64).
    { symmetry. apply (Z.mod_unique _ _ 1); lia. }
    lia.
Qed.

Lemma mid24_val_gen : forall (wb0 wb we x : word) n, bv_unsigned x = n -> bv_unsigned we = bv_unsigned wb + 24 * n -> 0 <= n <= CapLen.VD_MAXZ ->
  alu64 ALU_ADD wb0 (alu64 ALU_SUB (alu64 ALU_SLL x (wbv w5)) (alu64 ALU_SLL x (wbv w3))) = alu64 ALU_ADD wb0 (alu64 ALU_SUB we wb).
Proof.
  intros wb0 wb we x n Xu EQ RN. unfold CapLen.VD_MAXZ in RN.
  pose proof (bv_unsigned_in_range _ wb) as RB. pose proof (bv_unsigned_in_range _ we) as RE. rewrite bv_modulus_64 in RB, RE. unfold two64 in RB, RE.
  assert (SUBu : bv_unsigned (alu64 ALU_SUB we wb) = 24 * n).
  { cbn [alu64 alu]. rewrite bv_sub_unsigned. unfold bv_wrap. rewrite bv_modulus_64. unfold two64. rewrite Z.mod_small by lia. lia. }
  assert (SH3 : bv_unsigned (bv_and (wbv w3) (Z_to_bv 64 63)) = 3) by (rewrite shamt6_bv; reflexivity).
  assert (SH5 : bv_unsigned (bv_and (wbv w5) (Z_to_bv 64 63)) = 5) by (rewrite shamt6_bv; reflexivity).
  cbn [alu64 alu]. f_equal. apply bv_eq. cbn [alu64 alu] in SUBu.
  rewrite bv_sub_unsigned, !bv_shiftl_unsigned, SH3, SH5, Xu, !Z.shiftl_mul_pow2, SUBu by lia.
  change (2 ^ 5) with 32. change (2 ^ 3) with 8.
  unfold bv_wrap. rewrite bv_modulus_64. unfold two64.
  rewrite (Z.mod_small (n * 32)) by lia. rewrite (Z.mod_small (n * 8)) by lia.
  rewrite (Z.mod_small (n * 32 - n * 8)) by lia. lia.
Qed.
Lemma mid24_val : forall (wb we x : word) n, bv_unsigned x = n -> bv_unsigned we = bv_unsigned wb + 24 * n -> 0 <= n <= CapLen.VD_MAXZ ->
  alu64 ALU_ADD wb (alu64 ALU_SUB (alu64 ALU_SLL x (wbv w5)) (alu64 ALU_SLL x (wbv w3))) = we.
Proof.
  intros wb we x n Xu EQ RN. rewrite (mid24_val_gen wb wb we x n Xu EQ RN).
  pose proof (bv_unsigned_in_range _ wb) as RB. pose proof (bv_unsigned_in_range _ we) as RE. rewrite bv_modulus_64 in RB, RE. unfold two64 in RB, RE.
  unfold CapLen.VD_MAXZ in RN. cbn [alu64 alu]. apply bv_eq. rewrite bv_add_unsigned, bv_sub_unsigned.
  unfold bv_wrap. rewrite bv_modulus_64. unfold two64. rewrite (Z.mod_small (bv_unsigned we - bv_unsigned wb)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Theorem pkmid_sound : forall M_PC R, contract_sound segs OPS MP PB (pkmid_contract M_PC R).
Proof.
  intros M_PC R st sts Hpc HA K E ms model HS HMP HPB Hk. cbn [pkmid_contract c_apply] in HA. unfold pkmid_apply in HA.
  destruct (mid_of (s_facts st) (getr st R)) as [[[b0 e] b]|] eqn:MO; [|discriminate].
  destruct (negb (r5_eqb R X0)) eqn:RX; [|discriminate].
  pose proof (so_facts _ _ _ _ _ _ HS) as FH.
  destruct (mid_of_spec _ _ _ _ _ MO) as (x & CO & MV).
  assert (RX0 : R = X0 -> False) by (intros EQ; rewrite EQ in RX; cbn in RX; discriminate RX).
  destruct (same (s_facts st) e b) eqn:SEB.
  -
    injection HA as <-. apply (same_sound E _ _ _ FH) in SEB.
    pose proof (cnt_of2_val E _ x e b 0 FH CO ltac:(rewrite SEB; lia) ltac:(unfold CapLen.VD_MAXZ; lia)) as XV.
    refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP _).
    apply setreg_sound; [exact HS| exact RX0 |].
    rewrite MV. cbn [den].
    rewrite (mid24_val_gen (den E b0) (den E b) (den E b) (den E x) 0 XV ltac:(lia) ltac:(unfold CapLen.VD_MAXZ; lia)).
    cbn [alu64 alu]. apply bv_eq. rewrite bv_add_unsigned, bv_sub_unsigned, Z.sub_diag.
    unfold bv_wrap. rewrite bv_modulus_64. rewrite (Z.mod_small 0) by (unfold two64; lia). rewrite Z.add_0_r.
    pose proof (bv_unsigned_in_range _ (den E b0)) as RB0. rewrite bv_modulus_64 in RB0. apply Z.mod_small. exact RB0.
  - assert (GEO : exists n, bv_unsigned (den E e) = bv_unsigned (den E b) + 24 * n /\ 0 <= n <= CapLen.VD_MAXZ).
    { destruct (ghost_ok st b e) eqn:GO; [exact (ghost_ok_geom E st ms model b e HS GO)|].
      destruct (has_vd (s_facts st) b e) eqn:HV; [| discriminate HA]. exact (has_vd_geom E _ b e FH HV). }
    destruct ((if ghost_ok st b e then true else has_vd (s_facts st) b e)); [| discriminate HA].
    injection HA as <-. destruct GEO as (n & GEO & RN).
    pose proof (cnt_of2_val E _ x e b n FH CO GEO RN) as XV.
    refine (Hk _ (or_introl eq_refl) E ms model (env_ext_refl (s_next st) E) HMP _).
    apply setreg_sound; [exact HS| exact RX0 |].
    rewrite MV. unfold mid_val. destruct (same (s_facts st) b0 b) eqn:S0.
    + apply (same_sound E _ _ _ FH) in S0. cbn [den]. rewrite S0. exact (mid24_val _ _ _ n XV GEO RN).
    + rewrite !den_sv_alu. cbn [den]. exact (mid24_val_gen _ _ _ _ n XV GEO RN).
Qed.

End Sound.
End PkMid.
