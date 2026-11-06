(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module GNarrow.

Definition w32 : w64 := wlit 32%uint63.

Definition fold_srl32 (v : sv) : sv :=
  match v with
  | VAlu ALU_SRL x (VL c) => if weqb c w32 then sv_ext false 4%uint63 4%uint63 x else v
  | _ => v
  end.

Definition narrow (w : int) (v : sv) : sv :=
  let v1 := fold_srl32 v in
  let v2 := if PrimInt63.ltb w 8%uint63 && PrimInt63.ltb 0%uint63 w then sv_ext false 0%uint63 w v1 else v1 in
  match v2 with
  | VL _ => v2
  | _ => if sv_eqb v1 v then v else v2
  end.

Definition nar_cell (c : cell) : cell := Cell (c_idx c) (c_w c) (narrow (c_w c) (c_v c)).
Definition nar_gran (g : gran) : gran := Gran (g_dirty g) (List.map nar_cell (g_cells g)).
Definition nar_region (r : region) : region :=
  Region (rg_lo r) (rg_hi r) (rg_w r) (rg_bg r) (IMap.map nar_gran (rg_cells r)).

Section WithPc.
Variable S_PC : int.

Definition gnarrow_apply (st : sstate) : option (list sstate) :=
  Some [setregs st (IMap.map nar_region (s_regs st))].

Definition gnarrow_contract : contract := Contract S_PC gnarrow_apply.

Section Sound.
Variable segs : list Segment.
Variable OPS : optable.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma fold_srl32_den : forall E v, den E (fold_srl32 v) = den E v.
Proof.
  intros E v. unfold fold_srl32. destruct v as [| |op x c| | | | | | | |]; try reflexivity. destruct op; try reflexivity.
  destruct c as [c| | | | | | | | | |]; try reflexivity. destruct (weqb c w32) eqn:Q; [|reflexivity].
  apply (proj1 (weqb_ok _ _)) in Q. subst c.
  rewrite (den_sv_ext E false 4%uint63 4%uint63 x) by (unfold width_ok; change (to_Z 4%uint63) with 4; lia).
  change (to_Z 4%uint63) with 4. apply bv_eq. unfold ext_word. rewrite Z_to_bv_unsigned.
  cbn [den alu64 alu]. rewrite bv_shiftr_unsigned, shamt6_bv. change (to_Z (shamt6 w32)) with 32.
  pose proof (bv_unsigned_in_range _ (den E x)) as R. rewrite bv_modulus_64, two64_eq in R.
  unfold ext_Z. rewrite Z.shiftr_div_pow2 by lia. change (8 * 4) with 32.
  assert (D : 0 <= bv_unsigned (den E x) / 2 ^ 32 < 2 ^ 32).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite (Z.mod_small _ _ D). unfold bv_wrap. rewrite bv_modulus_64, two64_eq. apply Z.mod_small. lia.
Qed.

Lemma narrow_bytes : forall E w v i, 0 < to_Z w -> to_Z w <= 8 -> 0 <= i < to_Z w ->
  byte_of (den E (narrow w v)) i = byte_of (den E v) i.
Proof.
  intros E w v i W0 W8 Hi.
  assert (V2 : forall v1, den E v1 = den E v ->
            byte_of (den E (if PrimInt63.ltb w 8%uint63 && PrimInt63.ltb 0%uint63 w then sv_ext false 0%uint63 w v1 else v1)) i = byte_of (den E v) i).
  { intros v1 D1. destruct (PrimInt63.ltb w 8%uint63 && PrimInt63.ltb 0%uint63 w); [| rewrite D1; reflexivity].
    rewrite (den_sv_ext E false 0%uint63 w v1) by (unfold width_ok; change (to_Z 0%uint63) with 0; lia).
    change (to_Z 0%uint63) with 0. rewrite D1. apply bv_eq. rewrite !byte_of_zbyte by lia. unfold zbyte, ext_word.
    rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range _ (den E v)) as R. rewrite bv_modulus_64 in R.
    pose proof (ext_Z_range false 0 (to_Z w) (bv_unsigned (den E v)) ltac:(lia) ltac:(lia) ltac:(lia)) as ER.
    unfold bv_wrap. rewrite bv_modulus_64, (Z.mod_small _ _ ER).
    rewrite (ext_Z_byte 0 (to_Z w) (bv_unsigned (den E v)) i) by lia. rewrite Z.add_0_l. reflexivity. }
  unfold narrow. cbv zeta.
  pose proof (V2 (fold_srl32 v) (fold_srl32_den E v)) as H2.
  destruct (if PrimInt63.ltb w 8%uint63 && PrimInt63.ltb 0%uint63 w then sv_ext false 0%uint63 w (fold_srl32 v) else fold_srl32 v) eqn:Q;
    try exact H2; destruct (sv_eqb (fold_srl32 v) v); try reflexivity; exact H2.
Qed.

Lemma slot_sorted_nar : forall s, slot_sorted s -> slot_sorted (List.map nar_cell s).
Proof.
  induction s as [|c s IH]; intros H; [exact I|].
  destruct H as [H1 H2]. cbn [List.map]. split; [| exact (IH H2)].
  destruct s as [|c' s']; cbn [List.map]; [exact I|]. cbn [nar_cell c_idx c_w]. exact H1.
Qed.

Lemma region_ok_nar : forall priv E m k r, region_ok segs priv E m k r -> region_ok segs priv E m k (nar_region r).
Proof.
  intros priv E m k r RO.
  assert (HI : forall E0, hiZ E0 (nar_region r) = hiZ E0 r) by (intros; reflexivity).
  assert (LO : loZ (nar_region r) = loZ r) by reflexivity.
  assert (FIND : forall g gr, IMap.find g (rg_cells (nar_region r)) = Some gr -> exists gr0, IMap.find g (rg_cells r) = Some gr0 /\ gr = nar_gran gr0).
  { intros g gr F. cbn [nar_region rg_cells] in F. rewrite IMap.find_map in F. destruct (IMap.find g (rg_cells r)) as [gr0|]; [|discriminate].
    cbn [option_map] in F. injection F as <-. exists gr0. auto. }
  constructor.
  - cbn [nar_region rg_cells]. apply IMap.bst_map. exact (ro_bst _ _ _ _ _ _ RO).
  - rewrite HI, LO. exact (ro_range _ _ _ _ _ _ RO).
  - rewrite HI, LO. cbn [nar_region rg_w]. exact (ro_valid _ _ _ _ _ _ RO).
  - intros g gr F. destruct (FIND g gr F) as (gr0 & F0 & ->). cbn [nar_gran g_cells].
    destruct (ro_cells _ _ _ _ _ _ RO g gr0 F0) as [SS FC]. split; [exact (slot_sorted_nar _ SS)|].
    apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (c0 & <- & Hc0).
    pose proof (proj1 (Forall_forall _ _) FC c0 Hc0) as (C1 & C2 & C3 & C4). unfold cell_ok. cbn [nar_cell c_idx c_w c_v].
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. intros i Hi.
    rewrite (narrow_bytes E (c_w c0) (c_v c0) i C2 ltac:(lia) Hi). exact (C4 i Hi).
  - intros g gr c i F Hc Hi. rewrite HI, LO. destruct (FIND g gr F) as (gr0 & F0 & ->). cbn [nar_gran g_cells] in Hc.
    apply in_map_iff in Hc as (c0 & <- & Hc0). cbn [nar_cell c_idx c_w] in Hi |- *.
    exact (ro_cells_in _ _ _ _ _ _ RO g gr0 c0 i F0 Hc0 Hi).
  - intros o H1 H2 UC. rewrite HI, LO in H1.
    assert (UC' : uncovered r o).
    { intros g gr K0 F0. destruct (UC g (nar_gran gr) K0 ltac:(cbn [nar_region rg_cells]; rewrite IMap.find_map, F0; reflexivity)) as [D1 D2].
      cbn [nar_gran g_dirty g_cells] in D1, D2. split; [exact D1|].
      apply Forall_forall. intros c Hc. pose proof (proj1 (Forall_forall _ _) D2 (nar_cell c) (in_map _ _ _ Hc)) as X.
      unfold covers in *. cbn [nar_cell c_idx c_w] in X. exact X. }
    pose proof (ro_bg _ _ _ _ _ _ RO o H1 H2 UC') as BG. unfold bg_byte in BG |- *. cbn [nar_region rg_bg]. exact BG.
Qed.

Lemma st_ok_nar : forall E st ms mo, st_ok segs OPS E st ms mo -> st_ok segs OPS E (setregs st (IMap.map nar_region (s_regs st))) ms mo.
Proof.
  intros E st ms mo HS.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (FIND : forall k' r', IMap.find k' (IMap.map nar_region (s_regs st)) = Some r' -> exists r0, IMap.find k' (s_regs st) = Some r0 /\ r' = nar_region r0).
  { intros k' r' F. rewrite IMap.find_map in F. destruct (IMap.find k' (s_regs st)) as [r0|]; [|discriminate]. cbn [option_map] in F. injection F as <-. exists r0. auto. }
  assert (BASED : forall a, in_based E (IMap.map nar_region (s_regs st)) a <-> in_based E (s_regs st) a).
  { intros a. unfold in_based. split.
    - intros (k' & r' & F' & K' & R'). destruct (FIND k' r' F') as (r0 & F0 & ->). exists k', r0. auto.
    - intros (k' & r' & F' & K' & R'). exists k', (nar_region r'). split; [rewrite IMap.find_map, F'; reflexivity|]. split; [exact K'| exact R']. }
  constructor; cbn [setregs s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply IMap.bst_map. exact Pbst.
  - intros k' r' F'. destruct (FIND k' r' F') as (r0 & F0 & ->). apply region_ok_nar. exact (Preg k' r0 F0).
  - intros k1 r1 k2 r2 F1 F2 NE K1 K2 W a [A1 A2].
    destruct (FIND k1 r1 F1) as (q1 & G1 & ->). destruct (FIND k2 r2 F2) as (q2 & G2 & ->).
    exact (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2 W a (conj A1 A2)).
  - intros r0 g gr c F0 FG Hc. destruct (FIND _ r0 F0) as (q0 & Q0 & ->).
    cbn [nar_region rg_cells] in FG. rewrite IMap.find_map in FG. destruct (IMap.find g (rg_cells q0)) as [gr0|] eqn:FG0; [|discriminate].
    cbn [option_map] in FG. injection FG as <-. cbn [nar_gran g_cells] in Hc. apply in_map_iff in Hc as (c0 & <- & Hc0).
    cbn [nar_cell c_idx c_w]. exact (Ppub q0 g gr0 c0 Q0 FG0 Hc0).
  - unfold ops_apart in *. apply Forall_forall. intros o Ho a Ha. pose proof (proj1 (Forall_forall _ _) Papart o Ho a Ha) as [A B].
    split; [| exact B]. intros X. apply A. exact (proj1 (BASED a) X).
  - intros a FA. apply Pcov. destruct FA as [B|S]; [left; exact (proj1 (BASED a) B)| right; exact S].
Qed.

Theorem gnarrow_sound : contract_sound segs OPS MP PB gnarrow_contract.
Proof.
  intros st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [gnarrow_contract c_apply] in HAP. unfold gnarrow_apply in HAP. injection HAP as <-.
  exact (Hk _ (or_introl eq_refl) E ms model (env_ext_refl _ _) HMP (st_ok_nar E st ms model HS)).
Qed.

End Sound.
End WithPc.
End GNarrow.
