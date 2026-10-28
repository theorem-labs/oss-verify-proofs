(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module RK.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hv_slot (off : Z) (pins : list (nat * Z)) (q : nat) : expr :=
  if Nat.eqb q 2 then (if Z.eqb off 0 then EVar 2 else EAlu ALU_ADD (EVar 2) (ELit off))
  else match List.find (fun p => Nat.eqb (fst p) q) pins with Some p => ELit (snd p) | None => EVar (32 + q) end.
Definition hv_shape (sr : list expr) (off : Z) (pins : list (nat * Z)) : bool :=
  forallb (fun q => expr_eqb (nth q sr (ELit 0)) (hv_slot off pins q)) (seq 1 31).
Lemma regs_ok_hv : forall sr off pins sp0 R gh,
  hv_shape sr off pins = true -> 0 <= sp0 < 2 ^ 64 -> 0 <= sp0 + off < 2 ^ 64 ->
  getr R 2%bv = Z_to_bv 64 (sp0 + off) ->
  (forall q z, In (q, z) pins -> getr R (Z_to_bv 5 (Z.of_nat q)) = Z_to_bv 64 z) ->
  regs_ok (TK.hvE sp0 R gh) sr R.
Proof.
  intros sr off pins sp0 R gh Hsh Hsp Hspo H2 Hpins. apply APSX.regs_ok_pointwise. intros r Hr0.
  assert (Hq : In (ridx r) (seq 1 31)).
  { apply in_seq. pose proof (ridx_range r). assert (ridx r <> 0%nat).
    { intros X. apply Hr0. rewrite <- (ridx_roundtrip r), X. apply bv_eq. reflexivity. } lia. }
  unfold hv_shape in Hsh. rewrite forallb_forall in Hsh. specialize (Hsh _ Hq). apply expr_eqb_eq in Hsh. rewrite Hsh.
  unfold hv_slot. destruct (Nat.eqb (ridx r) 2) eqn:E2.
  - apply Nat.eqb_eq in E2. assert (r = 2%bv) by (rewrite <- (ridx_roundtrip r), E2; apply bv_eq; reflexivity). subst r.
    destruct (Z.eqb_spec off 0) as [->|Hne].
    + cbn [edenot ev TK.hvE]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite H2. f_equal. lia.
    + cbn [edenot ev TK.hvE]. unfold TK.hvV. cbn [Nat.ltb Nat.leb Nat.eqb]. rewrite TK.add_lit by lia. exact H2.
  - destruct (find (fun p => Nat.eqb (fst p) (ridx r)) pins) as [[q z]|] eqn:Hf.
    + apply find_some in Hf as [Hin Hq2]. cbn [fst] in Hq2. apply Nat.eqb_eq in Hq2. subst q. cbn [snd edenot].
      rewrite <- (Hpins _ _ Hin), ridx_roundtrip. reflexivity.
    + cbn [edenot]. symmetry. apply TK.hvE_reg.
Qed.

Definition ghl (l : list Z) : nat -> word := fun k => Z_to_bv 64 (nth k l 0).
Lemma ghl_u : forall sp0 R l k z, nth_error l k = Some z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ev (TK.hvE sp0 R (ghl l)) (64 + k)) = z.
Proof. intros sp0 R l k z H Hz. rewrite TK.hvE_ghost. unfold ghl. rewrite (nth_error_nth _ _ _ H). apply u64_of_Z. exact Hz. Qed.
Lemma hv_reg_u : forall sp0 R gh (r : reg) z, getr R r = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ev (TK.hvE sp0 R gh) (32 + ridx r)) = z.
Proof. intros sp0 R gh r z H Hz. rewrite TK.hvE_reg, H. apply u64_of_Z. exact Hz. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition probe_of (K : kentry) : option (expr * expr * bool) :=
  match K with
  | KRange (EAlu ALU_SLTU (EAlu ALU_SUB a b) (ELit 1)) lo hi =>
      if (Z.eqb lo 1 && Z.eqb hi 1)%bool then Some (a, b, true) else if (Z.eqb lo 0 && Z.eqb hi 0)%bool then Some (a, b, false) else None
  | _ => None
  end.
Fixpoint probes (l : list kentry) : list (expr * expr * bool) :=
  match l with [] => [] | K :: r => match probe_of K with Some p => p :: probes r | None => probes r end end.
Fixpoint pfacts (E : env) (l : list (expr * expr * bool)) : Prop :=
  match l with
  | [] => True
  | (a, b, true) :: r => edenot E a = edenot E b /\ pfacts E r
  | (a, b, false) :: r => edenot E a <> edenot E b /\ pfacts E r
  end.
Lemma sltu_sub1 : forall x y : word, bv_unsigned (alu64 ALU_SLTU (alu64 ALU_SUB x y) (Z_to_bv 64 1)) = if bv_eqb x y then 1 else 0.
Proof.
  intros x y. change (alu64 ALU_SLTU (alu64 ALU_SUB x y) (Z_to_bv 64 1)) with (if bv_ltu (x - y)%bv (Z_to_bv 64 1) then Z_to_bv 64 1 else Z_to_bv 64 0 : word).
  unfold bv_ltu, bv_eqb. rewrite bv_sub_unsigned. change (bv_unsigned (Z_to_bv 64 1)) with 1. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  pose proof (bv_unsigned_in_range _ x) as Hx. pose proof (bv_unsigned_in_range _ y) as Hy. change (bv_modulus 64) with (2 ^ 64) in Hx, Hy.
  destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [Heq|Hne].
  - rewrite Heq, Z.sub_diag. reflexivity.
  - assert (H : 1 <= (bv_unsigned x - bv_unsigned y) mod 2 ^ 64).
    { destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned y)).
      - rewrite <- (Z_mod_plus_full _ 1). rewrite Z.mod_small; lia.
      - rewrite Z.mod_small; lia. }
    destruct (Z.ltb_spec ((bv_unsigned x - bv_unsigned y) mod 2 ^ 64) 1); [lia | reflexivity].
Qed.
Lemma probe_of_sound : forall E (M : mem) K a b t, kentry_ok RSEGS E M K -> probe_of K = Some (a, b, t) ->
  if t then edenot E a = edenot E b else edenot E a <> edenot E b.
Proof.
  intros E M K a b t HK HP. destruct K as [| | | | |e lo hi| | | |]; try discriminate HP.
  destruct e as [| |op e1 e2| | | | |]; try discriminate HP. destruct op; try discriminate HP.
  destruct e1 as [| |op1 a1 b1| | | | |]; try discriminate HP. destruct op1; try discriminate HP.
  destruct e2 as [z| | | | | | |]; try discriminate HP. destruct z as [|p|p]; try discriminate HP. destruct p; try discriminate HP. cbn [probe_of] in HP.
  cbn [kentry_ok edenot] in HK. rewrite sltu_sub1 in HK. unfold bv_eqb in HK.
  destruct (Z.eqb lo 1 && Z.eqb hi 1)%bool eqn:B1.
  - injection HP as <- <- <-. apply andb_true_iff in B1 as [X1 X2]. apply Z.eqb_eq in X1, X2. subst lo hi.
    destruct (Z.eqb_spec (bv_unsigned (edenot E a1)) (bv_unsigned (edenot E b1))) as [X|X]; [apply bv_eq; exact X | lia].
  - destruct (Z.eqb lo 0 && Z.eqb hi 0)%bool eqn:B0; [|discriminate HP]. injection HP as <- <- <-.
    apply andb_true_iff in B0 as [X1 X2]. apply Z.eqb_eq in X1, X2. subst lo hi.
    destruct (Z.eqb_spec (bv_unsigned (edenot E a1)) (bv_unsigned (edenot E b1))) as [X|X]; [lia | intros Y; apply X; rewrite Y; reflexivity].
Qed.
Lemma probes_sound : forall E (M : mem) l, (forall K, In K l -> kentry_ok RSEGS E M K) -> pfacts E (probes l).
Proof.
  intros E M l. induction l as [|K r IH]; intros H; [exact I|]. cbn [probes].
  destruct (probe_of K) as [[[a b] t]|] eqn:HP; [|apply IH; intros K' HK'; apply H; right; exact HK'].
  pose proof (probe_of_sound E M K a b t (H K (or_introl eq_refl)) HP) as X.
  cbn [pfacts]. destruct t; (split; [exact X | apply IH; intros K' HK'; apply H; right; exact HK']).
Qed.
Lemma leaf_probes : forall c ps E' R' M M', CC.leaf_facts RSEGS c ps E' R' M M' -> pfacts E' (probes (SR.ps_cells ps)).
Proof. intros c ps E' R' M M' HLF. apply (probes_sound E' M'). exact (CC.lf_cells _ _ _ _ _ _ _ HLF). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma w_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 b -> a = b.
Proof. intros a b Ha Hb H. rewrite <- (u64_of_Z a Ha), <- (u64_of_Z b Hb), H. reflexivity. Qed.
Lemma w_neq : forall a b : Z, Z_to_bv 64 a <> Z_to_bv 64 b -> a <> b.
Proof. intros a b H X. apply H. rewrite X. reflexivity. Qed.
Lemma w_of_u : forall (w : word) z, bv_unsigned w = z -> w = Z_to_bv 64 z.
Proof. intros w z <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma ext_u8 : forall c, 0 <= c < 256 -> ext_val false 0 1 (Z_to_bv 64 c) = Z_to_bv 64 c.
Proof.
  intros c Hc. unfold ext_val, ext_Z. rewrite u64_of_Z by lia. change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite Z.div_1_r, Z.mod_small by lia. reflexivity.
Qed.
Lemma ext_u8_mod : forall c, 0 <= c < 2 ^ 64 -> ext_val false 0 1 (Z_to_bv 64 c) = Z_to_bv 64 (c mod 256).
Proof.
  intros c Hc. unfold ext_val, ext_Z. rewrite u64_of_Z by lia. change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 1)) with 256.
  rewrite Z.div_1_r. reflexivity.
Qed.
Lemma ext_s32 : forall c, 0 <= c < 2 ^ 31 -> ext_val true 0 4 (Z_to_bv 64 c) = Z_to_bv 64 c.
Proof.
  intros c Hc. unfold ext_val, ext_Z. rewrite u64_of_Z by lia. change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32).
  rewrite Z.div_1_r, Z.mod_small by lia. f_equal. unfold bv_swrap, bv_wrap. change (bv_half_modulus (8 * N.of_nat 4)) with (2 ^ 31). change (bv_modulus (8 * N.of_nat 4)) with (2 ^ 32).
  rewrite Z.mod_small by lia. lia.
Qed.
Lemma land_range : forall a b, 0 <= b < 2 ^ 64 -> 0 <= Z.land a b < 2 ^ 64.
Proof.
  intros a b Hb. assert (E : Z.land a b = Z.land a b mod 2 ^ 64).
  { rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. rewrite (Z.land_ones b) by lia. rewrite (Z.mod_small b) by lia. reflexivity. }
  rewrite E. apply Z.mod_pos_bound. lia.
Qed.
Lemma and_lit : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.land a b).
Proof.
  intros a b Ha Hb. change (alu64 ALU_AND (Z_to_bv 64 a) (Z_to_bv 64 b)) with (bv_and (Z_to_bv 64 a) (Z_to_bv 64 b)).
  apply bv_eq. rewrite bv_and_unsigned, !u64_of_Z by lia. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  symmetry. rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. rewrite (Z.land_ones b) by lia. rewrite (Z.mod_small b) by lia. reflexivity.
Qed.
Lemma add_w : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= a + b < 2 ^ 64 -> alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof. intros a b Ha Hb Hab. apply TK.add_lit; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma kword32_intro : forall E (M : mem) a v A z, estart E a = A -> 0 <= A -> A + 4 <= 2 ^ 64 -> edenot E v = Z_to_bv 64 z ->
  L5.u32_at RSEGS M A z -> kentry_ok RSEGS E M (KWord a 4 v).
Proof.
  intros E M a v A z Ha H0 H4 Hv Hu. cbn [kentry_ok]. assert (Hfl : flat E a (Z.of_nat 4)) by (unfold flat; rewrite Ha; lia).
  split; [lia|]. split; [exact Hfl|]. rewrite (CL5.adenot_start E a _ Hfl), Ha, Hv. exact Hu.
Qed.
Lemma kword8_elim : forall E (M : mem) a v A z, kentry_ok RSEGS E M (KWord a 1 v) -> estart E a = A -> bv_unsigned (edenot E v) = z -> L5.u8_at RSEGS M A z.
Proof.
  intros E M a v A z (_ & Hfl & Hr) Ha Hz. unfold L5.u8_at. rewrite <- Ha, <- (CL5.adenot_start E a _ Hfl), Hr, <- Hz. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_same : forall (M M' : mem) (n : nat) a bs, 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 a) n = Some bs -> rdn RSEGS M' (Z_to_bv 64 a) n = Some bs ->
  (forall i, a <= i < a + Z.of_nat n -> M (Z_to_bv 64 i) <> None) -> (forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) <> None) ->
  forall i, a <= i < a + Z.of_nat n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof.
  intros M M' n. induction n as [|n IH]; intros a bs Ha Hn H1 H2 D1 D2 i Hi; [lia|].
  cbn [rdn] in H1, H2. rewrite (L5C.add1_lit a) in H1, H2.
  pose proof (D1 a ltac:(lia)) as Da. pose proof (D2 a ltac:(lia)) as Da'.
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:EM; [|contradiction]. destruct (M' (Z_to_bv 64 a)) as [b'|] eqn:EM'; [|contradiction].
  destruct (rdn RSEGS M (Z_to_bv 64 (a + 1)) n) as [r1|] eqn:E1; [|discriminate]. destruct (rdn RSEGS M' (Z_to_bv 64 (a + 1)) n) as [r2|] eqn:E2; [|discriminate].
  injection H1 as <-. injection H2 as X Y. subst b' r2.
  destruct (Z.eq_dec i a) as [->|Hne]; [rewrite EM, EM'; reflexivity|].
  apply (IH (a + 1) r1); [lia | lia | exact E1 | exact E2 | intros j Hj; apply D1; lia | intros j Hj; apply D2; lia | lia].
Qed.
Lemma same_mem16 : forall (M M' : mem) A v1 v2, 0 <= A -> A + 16 <= 2 ^ 64 -> TK.samem (fun a => ~ (A <= a < A + 16)) M M' -> mem_grows M M' -> L5.defined M A 16 ->
  L5.u64_at RSEGS M A v1 -> L5.u64_at RSEGS M' A v1 -> L5.u64_at RSEGS M (A + 8) v2 -> L5.u64_at RSEGS M' (A + 8) v2 -> M' = M.
Proof.
  intros M M' A v1 v2 HA HA16 AG MG D C1 C1' C2 C2'. apply FunctionalExtensionality.functional_extensionality. intros x.
  rewrite <- (Z_to_bv_bv_unsigned 64 x). pose proof (bv_unsigned_in_range _ x) as Hx. change (bv_modulus 64) with (2 ^ 64) in Hx. set (z := bv_unsigned x) in *. clearbody z.
  assert (DM : forall i, A <= i < A + 16 -> M (Z_to_bv 64 i) <> None) by (intros i Hi; replace i with (A + (i - A)) by lia; apply D; lia).
  assert (DM' : forall i, A <= i < A + 16 -> M' (Z_to_bv 64 i) <> None) by (intros i Hi; apply MG; apply DM; exact Hi).
  destruct (Z_lt_le_dec z A) as [G1|G1]; [apply AG; [exact Hx | lia]|]. destruct (Z_le_gt_dec (A + 16) z) as [G2|G2]; [apply AG; [exact Hx | lia]|].
  destruct (Z_lt_le_dec z (A + 8)) as [G3|G3].
  - apply (rdn_same M M' 8%nat A _ HA ltac:(cbn; lia) C1 C1'); [intros i Hi; apply DM; cbn in Hi; lia | intros i Hi; apply DM'; cbn in Hi; lia | cbn; lia].
  - apply (rdn_same M M' 8%nat (A + 8) _ ltac:(lia) ltac:(cbn; lia) C2 C2'); [intros i Hi; apply DM; cbn in Hi; lia | intros i Hi; apply DM'; cbn in Hi; lia | cbn; lia].
Qed.
End RK.
