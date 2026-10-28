(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep PmCertKitG. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnValSP_u Bs0_code_r36afc_36b00_u Bs0_code_r36bf8_36bfc_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMVA.
Import PMS.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)).

(* [comment removed for export] *)
Lemma sub_in (A KS : list nat) : forallb (fun k => existsb (Nat.eqb k) KS) A = true -> forall k, In k A -> In k KS.
Proof.
  intros H k Hk. rewrite forallb_forall in H. specialize (H k Hk). apply existsb_exists in H. destruct H as (x & Hx & E). apply Nat.eqb_eq in E. subst x. exact Hx.
Qed.
(* [comment removed for export] *)
Definition VC : list nat := [2; 5; 6; 7; 8; 9; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 28; 29; 30; 31]%nat.
Definition KL : list nat := [1; 3; 4]%nat.
Ltac kin := apply sub_in; vm_compute; reflexivity.

Definition vconst (R : bvmap 5 word) (S e : Z) : Prop :=
  getr R (reg 2) = Z_to_bv 64 (S - 96) /\ getr R (reg 5) = Z_to_bv 64 2 /\ getr R (reg 6) = Z_to_bv 64 (-65) /\ getr R (reg 7) = Z_to_bv 64 239
  /\ getr R (reg 8) = Z_to_bv 64 240 /\ getr R (reg 9) = Z_to_bv 64 144 /\ getr R (reg 12) = Z_to_bv 64 e /\ getr R (reg 13) = Z_to_bv 64 8
  /\ getr R (reg 14) = Z_to_bv 64 (-1) /\ getr R (reg 15) = Z_to_bv 64 1 /\ getr R (reg 16) = Z_to_bv 64 (-62) /\ getr R (reg 17) = Z_to_bv 64 245
  /\ getr R (reg 18) = Z_to_bv 64 244 /\ getr R (reg 19) = Z_to_bv 64 143 /\ getr R (reg 20) = Z_to_bv 64 80240 /\ getr R (reg 21) = Z_to_bv 64 (-80241)
  /\ getr R (reg 22) = Z_to_bv 64 3 /\ getr R (reg 28) = Z_to_bv 64 224
  /\ getr R (reg 29) = Z_to_bv 64 160 /\ getr R (reg 30) = Z_to_bv 64 237 /\ getr R (reg 31) = Z_to_bv 64 159.
Lemma vconst_keep R R' S e : vconst R S e -> (forall k, In k VC -> getr R' (reg k) = getr R (reg k)) -> vconst R' S e.
Proof.
  intros (C2 & C5 & C6 & C7 & C8 & C9 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C28 & C29 & C30 & C31) K.
  unfold vconst. rewrite !K by (cbn; tauto). repeat split; assumption.
Qed.

(* [comment removed for export] *)
Lemma table_all : forallb (fun k => match rdn RSEGS (fun _ => None) (Z_to_bv 64 (80240 + Z.of_nat k)) 1 with Some [_] => true | _ => false end) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma table_ok k : 0 <= k < 256 -> exists b, rdn RSEGS (fun _ => None) (Z_to_bv 64 (80240 + k)) 1 = Some [b].
Proof.
  intros Hk. pose proof table_all as T. rewrite forallb_forall in T. specialize (T (Z.to_nat k) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in T by lia. destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 (80240 + k)) 1) as [[|b [|]]|]; try discriminate. exists b. reflexivity.
Qed.

Section Loop.
Variable M : word -> option byte.
Variables (S p e : Z).
Hypothesis RO : L5.img_clear M 65536 754672.
Hypothesis DEF : L5.defined M p (e - p).
Hypothesis HS : 140735332483168 <= S <= 2 ^ 47.
Hypothesis Hp : 1 <= p.
Hypothesis He : e <= 2 ^ 47.
Hypothesis Hn : e - p <= 2 ^ 26.

Definition goal_from (fx : FPState) (R : bvmap 5 word) (pc : Z) : Prop :=
  exists fx' R', msteps RSEGS (st fx R pc M) (st fx' R' 0x386e0 M) /\ getr R' (reg 2) = Z_to_bv 64 (S - 96) /\ (forall k, In k KL -> getr R' (reg k) = getr R (reg k)).

Lemma byte_at a : p <= a < e -> exists b, 0 <= b < 256 /\ L5.u8_at RSEGS M a b.
Proof. intros Ha. apply (PMCG.u8_of_defined RSEGS M a); [lia| lia|]. apply (L5.defined_sub M p (e - p)); [exact DEF| lia| lia]. Qed.

(* [comment removed for export] *)
Ltac epi MS KSx V :=
  lazymatch type of MS with msteps _ _ (@mkst ?fx2 ?R2 _ _ _) =>
    exists fx2, R2; split; [exact MS|]; split; [rewrite (KSx 2%nat) by PMK.inl; exact (proj1 V)|]; intros k Hk; apply KSx; revert k Hk; kin
  end.
Ltac split_exit H MS KS HR := destruct H as [MS H]; lazymatch type of H with
  | (forall x, _) /\ _ => destruct H as [KS HR]
  | _ => rename H into KS; assert (HR : True) by exact I
  end.

(* [comment removed for export] *)
Lemma join_case c (IH : forall fx R c', c < c' < e -> vconst R S e -> getr R (reg 10) = Z_to_bv 64 c' -> goal_from fx R 0x3855c) fx R c' :
  p <= c -> c < c' <= e -> vconst R S e -> getr R (reg 23) = Z_to_bv 64 c' -> goal_from fx R 0x386b8.
Proof.
  intros Hpc Hc V R23. pose proof V as (C2 & C5 & C6 & C7 & C8 & C9 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C28 & C29 & C30 & C31).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 10))) as B10. change (bv_modulus 64) with (2 ^ 64) in B10.
  LeanFeed.pfeed P (PMVAP.vaB_conc fx R M (fun j => match j with 2%nat => S | 33%nat => c' | 35%nat => e - c' | 37%nat => bv_unsigned (getr R (reg 10)) | _ => 0 end)) ltac:(first [ PMK.sc | (rewrite Z_to_bv_bv_unsigned; reflexivity) ]).
  destruct P as (fx1 & R1 & M1 & _ & FR & _ & EX). assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
  destruct EX as [(MS & KS & _)|(MS & KS & A10 & NE)].
  - epi MS KS V.
  - rewrite (Z.mod_small (c' + (e - c'))) in NE by lia. replace (c' + (e - c')) with e in NE by lia.
    assert (c' < e) by (destruct (Z.eq_dec c' e) as [->|]; [rewrite Z.sub_diag, Z.mod_0_l in NE by lia; lia| lia]).
    destruct (IH fx1 R1 c' ltac:(lia) (vconst_keep R R1 S e V ltac:(intros k Hk; apply KS; revert k Hk; kin)) A10) as (fx2 & R2 & MS2 & SP2 & KS2).
    exists fx2, R2. split; [eapply msteps_trans; [exact MS| exact MS2]|]. split; [exact SP2|]. intros k Hk. rewrite (KS2 k Hk). apply KS. revert k Hk; kin.
Qed.

Ltac get23 H := lazymatch type of H with
  | getr _ (PMK.reg 23) = _ /\ _ => constr:(proj1 H)
  | getr _ (PMK.reg 23) = _ => constr:(H)
  | _ /\ ?B => let H2 := constr:(proj2 H) in get23 H2
  end.
(* [comment removed for export] *)
Ltac leaf c IH V :=
  lazymatch goal with
  | H : msteps _ _ (@mkst _ _ (Z_to_bv 64 0x386e0) _ _) /\ _ |- _ =>
      let MS := fresh "MS" in let KS := fresh "KS" in let HR := fresh "HR" in split_exit H MS KS HR; epi MS KS V
  | H : msteps _ _ (@mkst ?fx2 ?R2 (Z_to_bv 64 0x386b8) _ _) /\ _ |- _ =>
      let MS := fresh "MS" in let KS := fresh "KS" in let HR := fresh "HR" in split_exit H MS KS HR;
      let t := get23 HR in let S6 := fresh "S6" in pose proof t as S6;
      let fx3 := fresh "fx" in let R3 := fresh "R" in let MS3 := fresh "MS" in let SP3 := fresh "SP" in let KS3 := fresh "KS" in
      lazymatch type of S6 with getr _ _ = Z_to_bv 64 ?cv =>
      destruct (join_case c IH fx2 R2 cv ltac:(lia) ltac:(lia) (vconst_keep _ R2 S e V ltac:(intros k Hk; apply KS; revert k Hk; kin)) S6) as (fx3 & R3 & MS3 & SP3 & KS3) end;
      exists fx3, R3; split; [eapply msteps_trans; [exact MS| exact MS3]|]; split; [exact SP3|]; intros k Hk; rewrite (KS3 k Hk); apply KS; revert k Hk; kin
  end.
Ltac leaves c IH V := repeat (lazymatch goal with H : _ \/ _ |- _ => destruct H as [H|H]; [leaf c IH V|] end); leaf c IH V.

Lemma goal_pre fx R pc fx2 R2 pc2 : msteps RSEGS (st fx R pc M) (st fx2 R2 pc2 M) -> (forall k, In k KL -> getr R2 (reg k) = getr R (reg k)) ->
  goal_from fx2 R2 pc2 -> goal_from fx R pc.
Proof.
  intros MS KS (fx3 & R3 & MS3 & SP3 & KS3). exists fx3, R3. split; [eapply msteps_trans; [exact MS| exact MS3]|]. split; [exact SP3|].
  intros k Hk. rewrite (KS3 k Hk). apply KS. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma slow c (IH : forall fx R c', c < c' < e -> vconst R S e -> getr R (reg 10) = Z_to_bv 64 c' -> goal_from fx R 0x3855c) fx R d0 b :
  p <= c -> c <= d0 < e -> 0 <= b < 256 -> vconst R S e -> getr R (reg 10) = Z_to_bv 64 d0 -> getr R (reg 11) = Z_to_bv 64 (b + 80240) ->
  getr R (reg 24) = Z_to_bv 64 b -> goal_from fx R 0x38600.
Proof.
  intros Hpc Hd Hb V R10 R11 R24. pose proof V as (C2 & C5 & C6 & C7 & C8 & C9 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C28 & C29 & C30 & C31).
  destruct (table_ok b Hb) as (tb & TB).
  assert (L1 : (25%bv : bv 5) <> 0%bv) by discriminate.
  assert (L2 : getr R (11%bv : bv 5) = Z_to_bv 64 (b + 80240)) by (replace (11%bv : bv 5) with (PMK.reg 11) by (apply bv_eq; reflexivity); exact R11).
  assert (L3 : rdn RSEGS M (Z_to_bv 64 (b + 80240 + bv_signed (0%bv : bv 12))) 1 = Some [tb]).
  { change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r, Z.add_comm. rewrite (PMCG.rdn_img RSEGS M 65536 754672 _ 1 RO) by lia. exact TB. }
  pose proof (PMCG.lbu_img_run RSEGS fx R M 0x38600 W_37578 25%bv 11%bv 0%bv (b + 80240) tb F_37578 eq_refl D_37578 L1 ltac:(lia) ltac:(lia) L2 ltac:(lia)
                ltac:(change (bv_signed (0%bv : bv 12)) with 0; lia) L3) as MSl.
  set (R2 := regupd R 25%bv (Z_to_bv 64 (bv_unsigned tb))) in MSl.
  assert (RU : forall k, k <> 25%nat -> (k < 32)%nat -> getr R2 (PMK.reg k) = getr R (PMK.reg k)).
  { intros k Hk Hk32. unfold R2. replace (25%bv : bv 5) with (PMK.reg 25) by (apply bv_eq; reflexivity). apply PMPX.regupd_other_idx; lia. }
  assert (R25 : getr R2 (PMK.reg 25) = Z_to_bv 64 (bv_unsigned tb)).
  { unfold R2. replace (25%bv : bv 5) with (PMK.reg 25) by (apply bv_eq; reflexivity). apply PMPX.regupd_same_idx. lia. }
  pose proof (bv_unsigned_in_range 8 tb) as Htb. change (bv_modulus 8) with 256 in Htb.
  assert (V2 : vconst R2 S e).
  { apply (vconst_keep R R2 S e V). intros k Hk. rewrite RU; [reflexivity| |]; unfold VC in Hk; cbn in Hk; repeat (destruct Hk as [<-|Hk]; [lia|]); destruct Hk. }
  assert (R2_10 : getr R2 (PMK.reg 10) = Z_to_bv 64 d0) by (rewrite RU by lia; exact R10).
  assert (R2_24 : getr R2 (PMK.reg 24) = Z_to_bv 64 b) by (rewrite RU by lia; exact R24).
  apply (goal_pre fx R 0x38600 fx R2 (0x38600 + 4) MSl).
  { intros k Hk. rewrite RU; [reflexivity| |]; unfold KL in Hk; cbn in Hk; repeat (destruct Hk as [<-|Hk]; [lia|]); destruct Hk. }
  change (0x38600 + 4) with 0x38604.
  clear MSl.
  pose proof V2 as (D2 & D5 & D6 & D7 & D8 & D9 & D12 & D13 & D14 & D15 & D16 & D17 & D18 & D19 & D20 & D21 & D22 & D28 & D29 & D30 & D31).
  set (t := bv_unsigned tb) in *.
  assert (CASES : t = 0 \/ t = 1 \/ t = 2 \/ t = 3 \/ 4 <= t) by lia.
  Local Ltac vfeed P := PMK.feed P ltac:(first [ PMK.sc | exact RO ]).
  destruct CASES as [Et|[Et|[Et|[Et|Et]]]].
  - rewrite Et in R25.
    LeanFeed.pfeed P (PMVAP.vaS2_0_conc fx R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | _ => 0 end)) ltac:(first [ PMK.sc | exact RO ]).
    destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
    leaves c IH V2.
  - rewrite Et in R25. destruct (Z_le_gt_dec (e - d0) 1) as [LE|GT].
    + LeanFeed.pfeed P (PMVAP.vaS2_1a_conc fx R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | _ => 0 end)) ltac:(first [ PMK.sc | exact RO ]).
      destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
      leaf c IH V2.
    + destruct (byte_at (d0 + 1) ltac:(lia)) as (b1 & Hb1 & U1).
      LeanFeed.pfeed P (PMVAP.vaS2_1b_conc fx R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | 39%nat => b1 | _ => 0 end)) ltac:(first [ PMK.sc | exact RO ]).
      destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
      leaves c IH V2.
  - rewrite Et in R25. destruct (Z_le_gt_dec (e - d0) 2) as [LE|GT].
    + LeanFeed.pfeed P (PMVAP.vaS2_2a_conc fx R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | _ => 0 end)) ltac:(first [ PMK.sc | exact RO ]).
      destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
      leaf c IH V2.
    + destruct (byte_at (d0 + 1) ltac:(lia)) as (b1 & Hb1 & U1). destruct (byte_at (d0 + 2) ltac:(lia)) as (b2 & Hb2 & U2).
      LeanFeed.pfeed P (PMVAP.vaS2_2b_conc fx R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b
                                                  | 39%nat => b1 | 40%nat => b2 | _ => 0 end)) ltac:(first [ PMK.sc | exact RO ]).
      destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
      leaves c IH V2.
  - rewrite Et in R25. destruct (Z_le_gt_dec (e - d0) 3) as [LE|GT].
    + LeanFeed.pfeed P (PMVAP.vaS2_3a_conc fx R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b | _ => 0 end)) ltac:(first [ PMK.sc | exact RO ]).
      destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
      leaf c IH V2.
    + destruct (byte_at (d0 + 1) ltac:(lia)) as (b1 & Hb1 & U1). destruct (byte_at (d0 + 2) ltac:(lia)) as (b2 & Hb2 & U2).
      destruct (byte_at (d0 + 3) ltac:(lia)) as (b3 & Hb3 & U3).
      LeanFeed.pfeed P (PMVAP.vaS2_3b_conc fx R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b
                                                  | 39%nat => b1 | 40%nat => b2 | 41%nat => b3 | _ => 0 end)) ltac:(first [ PMK.sc | exact RO ]).
      destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
      leaves c IH V2.
  - LeanFeed.pfeed P (PMVAP.vaS2_big_conc fx R2 M (fun j => match j with 2%nat => S | 33%nat => d0 | 35%nat => e - d0 | 37%nat => b
                                                 | 38%nat => t | _ => 0 end)) ltac:(first [ PMK.sc | exact RO ]).
    destruct P as (fx2 & R3 & M3 & _ & FR3 & _ & EX). assert (EM : M3 = M) by (apply functional_extensionality; exact FR3). subst M3.
    leaves c IH V2.
Qed.


Ltac get10 H := lazymatch type of H with
  | getr _ (PMK.reg 10) = _ /\ _ => constr:(proj1 H)
  | getr _ (PMK.reg 10) = _ => constr:(H)
  | _ /\ ?B => let H2 := constr:(proj2 H) in get10 H2
  end.
Ltac get11 H := lazymatch type of H with
  | getr _ (PMK.reg 11) = _ /\ _ => constr:(proj1 H)
  | getr _ (PMK.reg 11) = _ => constr:(H)
  | _ /\ ?B => let H2 := constr:(proj2 H) in get11 H2
  end.
Ltac get24 H := lazymatch type of H with
  | getr _ (PMK.reg 24) = _ /\ _ => constr:(proj1 H)
  | getr _ (PMK.reg 24) = _ => constr:(H)
  | _ /\ ?B => let H2 := constr:(proj2 H) in get24 H2
  end.
(* [comment removed for export] *)
Ltac fleaf c IH V R10 :=
  lazymatch goal with
  | H : msteps _ _ (@mkst ?fx2 ?R2 (Z_to_bv 64 0x38600) _ _) /\ _ |- _ =>
      let MS := fresh "MS" in let KS := fresh "KS" in let HR := fresh "HR" in split_exit H MS KS HR;
      let A10 := fresh "A10" in let A11 := fresh "A11" in let A24 := fresh "A24" in
      first [ let t := get10 HR in pose proof t as A10 | assert (A10 := eq_trans (KS 10%nat ltac:(PMK.inl)) R10) ];
      let t11 := get11 HR in pose proof t11 as A11; let t24 := get24 HR in pose proof t24 as A24;
      lazymatch type of A10 with getr _ _ = Z_to_bv 64 ?dv => lazymatch type of A24 with getr _ _ = Z_to_bv 64 ?bv =>
        apply (goal_pre _ _ _ fx2 R2 _ MS ltac:(intros k Hk; apply KS; revert k Hk; kin));
        apply (slow c IH fx2 R2 dv bv ltac:(lia) ltac:(lia) ltac:(lia) (vconst_keep _ R2 S e V ltac:(intros k Hk; apply KS; revert k Hk; kin)) A10 A11 A24) end end
  | H : msteps _ _ (@mkst ?fx2 ?R2 (Z_to_bv 64 0x386b8) _ _) /\ _ |- _ =>
      let MS := fresh "MS" in let KS := fresh "KS" in let HR := fresh "HR" in split_exit H MS KS HR;
      let t := get23 HR in let S6 := fresh "S6" in pose proof t as S6;
      lazymatch type of S6 with getr _ _ = Z_to_bv 64 ?cv =>
        apply (goal_pre _ _ _ fx2 R2 _ MS ltac:(intros k Hk; apply KS; revert k Hk; kin));
        apply (join_case c IH fx2 R2 cv ltac:(lia) ltac:(lia) (vconst_keep _ R2 S e V ltac:(intros k Hk; apply KS; revert k Hk; kin)) S6) end
  end.
Ltac fleaves c IH V R10 := repeat (lazymatch goal with H : _ \/ _ |- _ => destruct H as [H|H]; [fleaf c IH V R10|] end); fleaf c IH V R10.

Lemma loop_head : forall (n : nat) fx R c, Z.to_nat (e - c) = n -> p <= c < e -> vconst R S e -> getr R (reg 10) = Z_to_bv 64 c -> goal_from fx R 0x3855c.
Proof.
  intros n. induction n as [n IHn] using (well_founded_induction Wf_nat.lt_wf). intros fx R c Hn' Hc V R10.
  assert (IH : forall fx R c', c < c' < e -> vconst R S e -> getr R (reg 10) = Z_to_bv 64 c' -> goal_from fx R 0x3855c).
  { intros fx' R' c' Hc' V' R10'. apply (IHn (Z.to_nat (e - c')) ltac:(lia) fx' R' c'); [reflexivity| lia| exact V'| exact R10']. }
  pose proof V as (C2 & C5 & C6 & C7 & C8 & C9 & C12 & C13 & C14 & C15 & C16 & C17 & C18 & C19 & C20 & C21 & C22 & C28 & C29 & C30 & C31).
  destruct (Z_le_gt_dec 8 (e - c)) as [GE|LT].
  - destruct (byte_at c ltac:(lia)) as (b0 & Hb0 & U0). destruct (byte_at (c + 1) ltac:(lia)) as (b1 & Hb1 & U1).
    destruct (byte_at (c + 2) ltac:(lia)) as (b2 & Hb2 & U2). destruct (byte_at (c + 3) ltac:(lia)) as (b3 & Hb3 & U3).
    destruct (byte_at (c + 4) ltac:(lia)) as (b4 & Hb4 & U4). destruct (byte_at (c + 5) ltac:(lia)) as (b5 & Hb5 & U5).
    destruct (byte_at (c + 6) ltac:(lia)) as (b6 & Hb6 & U6). destruct (byte_at (c + 7) ltac:(lia)) as (b7 & Hb7 & U7).
    LeanFeed.pfeed P (PMVAP.vaF8_conc fx R M (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | 36%nat => b0 | 37%nat => b1 | 38%nat => b2
        | 39%nat => b3 | 40%nat => b4 | 41%nat => b5 | 42%nat => b6 | 43%nat => b7 | _ => 0 end)) ltac:(first [ PMK.sc ]).
    destruct P as (fx1 & R1 & M1 & _ & FR & _ & EX). assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
    fleaves c IH V R10.
  - destruct (byte_at c ltac:(lia)) as (b0 & Hb0 & U0).
    LeanFeed.pfeed P (PMVAP.vaF1_conc fx R M (fun j => match j with 2%nat => S | 33%nat => c | 35%nat => e - c | 36%nat => b0 | _ => 0 end)) ltac:(first [ PMK.sc ]).
    destruct P as (fx1 & R1 & M1 & _ & FR & _ & MS & KS & A11 & A24). assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
    apply (goal_pre _ _ _ fx1 R1 _ MS ltac:(intros k Hk; apply KS; revert k Hk; kin)).
    apply (slow c IH fx1 R1 c b0 ltac:(lia) ltac:(lia) ltac:(lia) (vconst_keep _ R1 S e V ltac:(intros k Hk; apply KS; revert k Hk; kin))); [| exact A11| exact A24].
    rewrite (KS 10%nat) by PMK.inl. exact R10.
Qed.
End Loop.

Lemma e6 : Z_to_bv 64 18446744073709551551 = Z_to_bv 64 (-65). Proof. apply bv_eq. reflexivity. Qed.
Lemma e14 : Z_to_bv 64 18446744073709551615 = Z_to_bv 64 (-1). Proof. apply bv_eq. reflexivity. Qed.
Lemma e16 : Z_to_bv 64 18446744073709551554 = Z_to_bv 64 (-62). Proof. apply bv_eq. reflexivity. Qed.
Lemma e21 : Z_to_bv 64 18446744073709471375 = Z_to_bv 64 (-80241). Proof. apply bv_eq. reflexivity. Qed.

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Hypothesis LY : PMS.layout L.

Theorem validate_ok : PMS.validate_spec L.
Proof.
  unfold PMS.validate_spec, PMSP.validate_spec, PMSP.scan_spec.
  intros fx R M model K p n sp r Mh Ml K0 ENT A10 A11 Hn Hp HNP Hpn DEF DISJ BASE KONT.
  destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *.
  pose proof (L5C.stk_writable RSEGS _ M sp _ STK) as WR0.
  pose proof BASE as (RO & _ & _ & _). cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in RO.
  unfold PMSP.cfg. cbn [pa_validate AD PnLayoutS_u.ADDR_S].
  assert (Hsp : 0 <= sp < 2 ^ 64) by lia.
  assert (FB : forall M', (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 96 <= i < sp - 96 + 96) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
                 L5.frame_but [(sp - (12288 + 2048 * 0), 12288 + 2048 * 0)] M M').
  { intros M' FRZ x Hx. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply FRZ; [apply (bv_unsigned_in_range 64)|].
    intros X. apply (Hx (sp - (12288 + 2048 * 0), 12288 + 2048 * 0)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
  destruct (Z_le_gt_dec p 0) as [Ep|Ep].
  { assert (En0 : n = 0) by (destruct HNP; lia).
    LeanFeed.pfeed P (PMVAP.vaEz_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => p | 35%nat => n | _ => 0 end)) ltac:(first [ PMK.sc | (apply (L5.writable_sub RSEGS M (sp - (12288 + 2048 * 0)) (12288 + 2048 * 0)); [exact WR0| lia| lia]) ]).
    destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS & KS & _).
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| exact MS|].
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x38714 W_37674 r F_37674 ltac:(reflexivity) D_37674); [| exact RA1| exact RA2]|].
    { rewrite (KS 1%nat) by PMK.inl. exact Rra. }
    apply (KONT fx1 R1 M1).
    + apply PMK.preserved_by_index. intros k Hk. apply KS. revert k Hk. kin.
    + apply FB. exact FRZ1.
    + exact MG1. }
  LeanFeed.pfeed P (PMVAP.vaE_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => p | 35%nat => n | _ => 0 end)) ltac:(first [ PMK.sc | (apply (L5.writable_sub RSEGS M (sp - (12288 + 2048 * 0)) (12288 + 2048 * 0)); [exact WR0| lia| lia]) ]).
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & EX).
  destruct EX as [(MS & KS & _)|(MS & KS & E2 & E5 & E6 & E7 & E8 & E9 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E28 & E29 & E30 & E31
                                 & Hn0 & S96 & S88 & S80 & S72 & S64 & S56 & S48 & S40 & S32 & S24 & S16b & S8)].
  - (* [comment removed for export] *)
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| exact MS|].
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x38714 W_37674 r F_37674 ltac:(reflexivity) D_37674); [| exact RA1| exact RA2]|].
    { rewrite (KS 1%nat) by PMK.inl. exact Rra. }
    apply (KONT fx1 R1 M1).
    + apply PMK.preserved_by_index. intros k Hk. apply KS. revert k Hk. kin.
    + apply FB. exact FRZ1.
    + exact MG1.
  - rewrite Z.sub_0_r, Z.mod_small in Hn0 by lia.
    assert (RO1 : L5.img_clear M1 65536 754672) by (intros i Hi; rewrite FRZ1 by lia; apply RO; exact Hi).
    assert (DEF1 : L5.defined M1 p (p + n - p)).
    { replace (p + n - p) with n by lia. intros i Hi. rewrite FRZ1 by lia. apply DEF. exact Hi. }
    assert (V : vconst R1 sp (p + n)).
    { unfold vconst. rewrite e6 in E6. rewrite e14 in E14. rewrite e16 in E16. rewrite e21 in E21. repeat split; assumption. }
    destruct (loop_head M1 sp p (p + n) RO1 DEF1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (Z.to_nat n) fx1 R1 p ltac:(lia) ltac:(lia) V
                ltac:(rewrite (KS 10%nat) by PMK.inl; exact A10)) as (fx2 & R2 & MS2 & SP2 & KS2).
    pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as V8. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as V9.
    pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as V18. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as V19.
    pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 20))) as V20. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 21))) as V21.
    pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 22))) as V22. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 23))) as V23.
    pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 24))) as V24. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 25))) as V25.
    pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 26))) as V26. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 27))) as V27. change (bv_modulus 64) with (2 ^ 64) in *.
    assert (WR1 : L5.writable RSEGS M1 (sp - 96) 96).
    { apply (L5.writable_grows RSEGS M M1 _ _ MG1). apply (L5.writable_sub RSEGS M (sp - (12288 + 2048 * 0)) (12288 + 2048 * 0)); [exact WR0| lia| lia]. }
    LeanFeed.pfeed P (PMVAP.vaX_conc fx2 R2 M1 (fun j => match j with 2%nat => sp | 45%nat => bv_unsigned (getr R (PMK.reg 8)) | 46%nat => bv_unsigned (getr R (PMK.reg 9))
        | 47%nat => bv_unsigned (getr R (PMK.reg 18)) | 48%nat => bv_unsigned (getr R (PMK.reg 19)) | 49%nat => bv_unsigned (getr R (PMK.reg 20))
        | 50%nat => bv_unsigned (getr R (PMK.reg 21)) | 51%nat => bv_unsigned (getr R (PMK.reg 22)) | 52%nat => bv_unsigned (getr R (PMK.reg 23))
        | 53%nat => bv_unsigned (getr R (PMK.reg 24)) | 54%nat => bv_unsigned (getr R (PMK.reg 25)) | 55%nat => bv_unsigned (getr R (PMK.reg 26))
        | 56%nat => bv_unsigned (getr R (PMK.reg 27)) | _ => 0 end)) ltac:(first [ PMK.sc ]).
    destruct P as (fx3 & R3 & M3 & _ & FR3 & _ & MS3 & KS3 & X2 & X8 & X9 & X18 & X19 & X20 & X21 & X22 & X23 & X24 & X25 & X26 & X27).
    assert (EM : M3 = M1) by (apply functional_extensionality; exact FR3). subst M3.
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| eapply msteps_trans; [exact MS| eapply msteps_trans; [exact MS2| exact MS3]]|].
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx3 R3 M1 0x38714 W_37674 r F_37674 ltac:(reflexivity) D_37674); [| exact RA1| exact RA2]|].
    { rewrite (KS3 1%nat) by PMK.inl. rewrite (KS2 1%nat) by PMK.inl. rewrite (KS 1%nat) by PMK.inl. exact Rra. }
    apply (KONT fx3 R3 M1).
    + apply PMK.preserved_by_index. intros k Hk. unfold PMK.cs_all in Hk. cbn in Hk.
      destruct Hk as [<-|Hk]; [rewrite X2, Rsp; reflexivity|].
      destruct Hk as [<-|Hk]; [rewrite (KS3 3%nat), (KS2 3%nat), (KS 3%nat) by PMK.inl; reflexivity|].
      destruct Hk as [<-|Hk]; [rewrite (KS3 4%nat), (KS2 4%nat), (KS 4%nat) by PMK.inl; reflexivity|].
      destruct Hk as [<-|Hk]; [rewrite X8; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite X9; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite X18; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite X19; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite X20; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite X21; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite X22; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite X23; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite X24; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite X25; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite X26; apply Z_to_bv_bv_unsigned|].
      destruct Hk as [<-|Hk]; [rewrite X27; apply Z_to_bv_bv_unsigned|].
      destruct Hk.
    + apply FB. exact FRZ1.
    + exact MG1.
Qed.

End Stage.
End PMVA.
