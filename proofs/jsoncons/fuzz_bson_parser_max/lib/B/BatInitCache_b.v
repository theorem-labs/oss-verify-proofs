(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0_code_r41498_42984_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000000. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

(* [comment removed for export] *)
Definition art_ic_size (c : Z) : Z := if c =? 31 then 64 else AsanTab.class_size c.
Definition art_ic_mc (c : Z) : Z := 2 * Z.max 1 (Z.min 8 (1024 / art_ic_size c)).
(* [comment removed for export] *)
Fixpoint art_ic_mem (M : word -> option byte) (ca : Z) (k : nat) : word -> option byte :=
  match k with
  | O => M
  | S k' => Wn 8 (Wn 4 (art_ic_mem M ca k') (ca + 80 * Z.of_nat k + 4) (art_ic_mc (Z.of_nat k))) (ca + 80 * Z.of_nat k + 8) (art_ic_size (Z.of_nat k))
  end.

Lemma art_ic_mem_S : forall M ca k,
  art_ic_mem M ca (S k) = Wn 8 (Wn 4 (art_ic_mem M ca k) (ca + 80 * (Z.of_nat k + 1) + 4) (art_ic_mc (Z.of_nat k + 1))) (ca + 80 * (Z.of_nat k + 1) + 8) (art_ic_size (Z.of_nat k + 1)).
Proof. intros. cbn [art_ic_mem]. rewrite Nat2Z.inj_succ, <- Z.add_1_r. reflexivity. Qed.

Lemma art_ic_size_pos : forall c, 1 <= c <= 31 -> 32 <= art_ic_size c <= 65536.
Proof.
  intros c Hc. unfold art_ic_size.
  assert (H : forall x, In x (map (fun i => Z.of_nat i) (seq 1 31)) -> 32 <= (if x =? 31 then 64 else AsanTab.class_size x) <= 65536).
  { intros x Hx. cbn in Hx. repeat (destruct Hx as [<-|Hx]; [vm_compute; split; discriminate|]). destruct Hx. }
  apply H. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma art_ic_mc_range : forall c, 1 <= c <= 31 -> 2 <= art_ic_mc c <= 16.
Proof. intros c Hc. unfold art_ic_mc. pose proof (art_ic_size_pos c Hc). split; [lia|]. assert (Z.min 8 (1024 / art_ic_size c) <= 8) by lia. lia. Qed.

Lemma art_ic_mem_grows : forall M ca k, mem_grows M (art_ic_mem M ca k).
Proof. induction k; [apply mem_grows_refl|]. rewrite art_ic_mem_S. eapply mem_grows_trans; [exact IHk|]. eapply mem_grows_trans; apply Wn_grows. Qed.

Lemma wr_ic : forall M ca k a n, wrA M a n -> wrA (art_ic_mem M ca k) a n.
Proof. intros. eapply wr_grows; [apply art_ic_mem_grows|assumption]. Qed.
Lemma wok_ic : forall M ca k a n, wokA M a n -> wokA (art_ic_mem M ca k) a n.
Proof. intros. eapply wok_grows; [apply art_ic_mem_grows|assumption]. Qed.

(* [comment removed for export] *)
Lemma art_ic_mem_outside : forall M ca k (x : word), 0 <= ca -> ca + 4096 < 2 ^ 64 -> (k <= 31)%nat ->
  ~ (ca + 84 <= U x < ca + 80 * Z.of_nat k + 16) -> art_ic_mem M ca k x = M x.
Proof.
  induction k; intros x Hca Hca' Hk N; [reflexivity|]. rewrite art_ic_mem_S.
  rewrite Nat2Z.inj_succ in N.
  rewrite 2 Wn_outside by (cbn; lia). apply IHk; [lia|lia|lia|cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma cell_ic_other : forall M ca k a n v, 0 <= ca -> ca + 4096 < 2 ^ 64 -> (k <= 31)%nat -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  (forall c, 1 <= c <= Z.of_nat k -> apart (ca + 80 * c + 4) 12 a (Z.of_nat n)) ->
  cellA M a n v -> cellA (art_ic_mem M ca k) a n v.
Proof.
  induction k; intros a n v Hca Hca' Hk Ha Han AP C; [exact C|]. rewrite art_ic_mem_S.
  pose proof (AP (Z.of_nat k + 1) ltac:(rewrite Nat2Z.inj_succ; lia)) as A1. unfold apart in A1.
  apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|].
  apply cell_Wn_other; [lia|cbn; lia|lia|lia|unfold apart; cbn; lia|].
  apply IHk; [lia|lia|lia|lia|lia| |exact C]. intros c Hc. apply AP. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma cell_ic_count : forall M ca k c v, 0 <= ca -> ca + 4096 < 2 ^ 64 -> (k <= 31)%nat -> 0 <= c <= 31 ->
  cellA M (ca + 80 * c) 4 v -> cellA (art_ic_mem M ca k) (ca + 80 * c) 4 v.
Proof. intros. apply cell_ic_other; [lia|lia|assumption|lia|cbn; lia| intros c' Hc'; unfold apart; cbn; lia | assumption]. Qed.

Lemma cell_ic_mc : forall M ca k c, 0 <= ca -> ca + 4096 < 2 ^ 64 -> (k <= 31)%nat -> 1 <= c <= Z.of_nat k ->
  cellA (art_ic_mem M ca k) (ca + 80 * c + 4) 4 (art_ic_mc c).
Proof.
  induction k; intros c Hca Hca' Hk Hc; [lia|]. rewrite art_ic_mem_S. rewrite Nat2Z.inj_succ in Hc.
  destruct (Z.eq_dec c (Z.of_nat k + 1)) as [->|NE].
  - apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]. apply cell_Wn_hit; [lia|cbn; lia].
  - do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]). apply IHk; lia.
Qed.

Lemma cell_ic_size : forall M ca k c, 0 <= ca -> ca + 4096 < 2 ^ 64 -> (k <= 31)%nat -> 1 <= c <= Z.of_nat k ->
  cellA (art_ic_mem M ca k) (ca + 80 * c + 8) 8 (art_ic_size c).
Proof.
  induction k; intros c Hca Hca' Hk Hc; [lia|]. rewrite art_ic_mem_S. rewrite Nat2Z.inj_succ in Hc.
  destruct (Z.eq_dec c (Z.of_nat k + 1)) as [->|NE].
  - apply cell_Wn_hit; [lia|cbn; lia].
  - do 2 (apply cell_Wn_other; [lia|cbn; lia|lia|cbn; lia|unfold apart; cbn; lia|]). apply IHk; lia.
Qed.

(* [comment removed for export] *)
Definition art_ic_kept (r : reg) : Prop := r <> 11%bv /\ r <> 13%bv /\ r <> 15%bv /\ r <> 28%bv /\ r <> 29%bv /\ r <> 30%bv.

Section FPX. Context {fx : PropExec.FPState}.
(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_1 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 88) -> getr regs 13 = Z_to_bv 64 32 -> getr regs 15 = Z_to_bv 64 18446744073709551601 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 1 + 4) (art_ic_mc 1)) (ca + 80 * 1 + 8) (art_ic_size 1)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 168) /\ getr regs' 13 = Z_to_bv 64 64 /\ getr regs' 15 = Z_to_bv 64 18446744073709551602
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbft F_5714c D_5714c.
    zstep F_57150 D_57150.
    stepn F_57154 D_57154.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 1 + 4) (art_ic_mc 1) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 1 + 8) (art_ic_size 1) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_2 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 168) -> getr regs 13 = Z_to_bv 64 64 -> getr regs 15 = Z_to_bv 64 18446744073709551602 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 2 + 4) (art_ic_mc 2)) (ca + 80 * 2 + 8) (art_ic_size 2)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 248) /\ getr regs' 13 = Z_to_bv 64 96 /\ getr regs' 15 = Z_to_bv 64 18446744073709551603
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbft F_5714c D_5714c.
    zstep F_57150 D_57150.
    stepn F_57154 D_57154.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 2 + 4) (art_ic_mc 2) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 2 + 8) (art_ic_size 2) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_3 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 248) -> getr regs 13 = Z_to_bv 64 96 -> getr regs 15 = Z_to_bv 64 18446744073709551603 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 3 + 4) (art_ic_mc 3)) (ca + 80 * 3 + 8) (art_ic_size 3)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 328) /\ getr regs' 13 = Z_to_bv 64 128 /\ getr regs' 15 = Z_to_bv 64 18446744073709551604
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbft F_5714c D_5714c.
    zstep F_57150 D_57150.
    stepn F_57154 D_57154.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 3 + 4) (art_ic_mc 3) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 3 + 8) (art_ic_size 3) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_4 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 328) -> getr regs 13 = Z_to_bv 64 128 -> getr regs 15 = Z_to_bv 64 18446744073709551604 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 4 + 4) (art_ic_mc 4)) (ca + 80 * 4 + 8) (art_ic_size 4)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 408) /\ getr regs' 13 = Z_to_bv 64 160 /\ getr regs' 15 = Z_to_bv 64 18446744073709551605
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbft F_5714c D_5714c.
    zstep F_57150 D_57150.
    stepn F_57154 D_57154.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 4 + 4) (art_ic_mc 4) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 4 + 8) (art_ic_size 4) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_5 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 408) -> getr regs 13 = Z_to_bv 64 160 -> getr regs 15 = Z_to_bv 64 18446744073709551605 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 5 + 4) (art_ic_mc 5)) (ca + 80 * 5 + 8) (art_ic_size 5)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 488) /\ getr regs' 13 = Z_to_bv 64 192 /\ getr regs' 15 = Z_to_bv 64 18446744073709551606
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 5 + 4) (art_ic_mc 5) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 5 + 8) (art_ic_size 5) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_6 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 488) -> getr regs 13 = Z_to_bv 64 192 -> getr regs 15 = Z_to_bv 64 18446744073709551606 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 6 + 4) (art_ic_mc 6)) (ca + 80 * 6 + 8) (art_ic_size 6)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 568) /\ getr regs' 13 = Z_to_bv 64 224 /\ getr regs' 15 = Z_to_bv 64 18446744073709551607
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 6 + 4) (art_ic_mc 6) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 6 + 8) (art_ic_size 6) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_7 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 568) -> getr regs 13 = Z_to_bv 64 224 -> getr regs 15 = Z_to_bv 64 18446744073709551607 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 7 + 4) (art_ic_mc 7)) (ca + 80 * 7 + 8) (art_ic_size 7)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 648) /\ getr regs' 13 = Z_to_bv 64 256 /\ getr regs' 15 = Z_to_bv 64 18446744073709551608
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 7 + 4) (art_ic_mc 7) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 7 + 8) (art_ic_size 7) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_8 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 648) -> getr regs 13 = Z_to_bv 64 256 -> getr regs 15 = Z_to_bv 64 18446744073709551608 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 8 + 4) (art_ic_mc 8)) (ca + 80 * 8 + 8) (art_ic_size 8)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 728) /\ getr regs' 13 = Z_to_bv 64 288 /\ getr regs' 15 = Z_to_bv 64 18446744073709551609
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 8 + 4) (art_ic_mc 8) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 8 + 8) (art_ic_size 8) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_9 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 728) -> getr regs 13 = Z_to_bv 64 288 -> getr regs 15 = Z_to_bv 64 18446744073709551609 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 9 + 4) (art_ic_mc 9)) (ca + 80 * 9 + 8) (art_ic_size 9)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 808) /\ getr regs' 13 = Z_to_bv 64 320 /\ getr regs' 15 = Z_to_bv 64 18446744073709551610
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 9 + 4) (art_ic_mc 9) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 9 + 8) (art_ic_size 9) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_10 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 808) -> getr regs 13 = Z_to_bv 64 320 -> getr regs 15 = Z_to_bv 64 18446744073709551610 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 10 + 4) (art_ic_mc 10)) (ca + 80 * 10 + 8) (art_ic_size 10)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 888) /\ getr regs' 13 = Z_to_bv 64 352 /\ getr regs' 15 = Z_to_bv 64 18446744073709551611
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 10 + 4) (art_ic_mc 10) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 10 + 8) (art_ic_size 10) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_11 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 888) -> getr regs 13 = Z_to_bv 64 352 -> getr regs 15 = Z_to_bv 64 18446744073709551611 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 11 + 4) (art_ic_mc 11)) (ca + 80 * 11 + 8) (art_ic_size 11)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 968) /\ getr regs' 13 = Z_to_bv 64 384 /\ getr regs' 15 = Z_to_bv 64 18446744073709551612
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 11 + 4) (art_ic_mc 11) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 11 + 8) (art_ic_size 11) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_12 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 968) -> getr regs 13 = Z_to_bv 64 384 -> getr regs 15 = Z_to_bv 64 18446744073709551612 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 12 + 4) (art_ic_mc 12)) (ca + 80 * 12 + 8) (art_ic_size 12)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 1048) /\ getr regs' 13 = Z_to_bv 64 416 /\ getr regs' 15 = Z_to_bv 64 18446744073709551613
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 12 + 4) (art_ic_mc 12) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 12 + 8) (art_ic_size 12) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_13 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 1048) -> getr regs 13 = Z_to_bv 64 416 -> getr regs 15 = Z_to_bv 64 18446744073709551613 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 13 + 4) (art_ic_mc 13)) (ca + 80 * 13 + 8) (art_ic_size 13)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 1128) /\ getr regs' 13 = Z_to_bv 64 448 /\ getr regs' 15 = Z_to_bv 64 18446744073709551614
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 13 + 4) (art_ic_mc 13) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 13 + 8) (art_ic_size 13) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_14 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 1128) -> getr regs 13 = Z_to_bv 64 448 -> getr regs 15 = Z_to_bv 64 18446744073709551614 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 14 + 4) (art_ic_mc 14)) (ca + 80 * 14 + 8) (art_ic_size 14)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 1208) /\ getr regs' 13 = Z_to_bv 64 480 /\ getr regs' 15 = Z_to_bv 64 18446744073709551615
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 14 + 4) (art_ic_mc 14) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 14 + 8) (art_ic_size 14) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_15 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 1208) -> getr regs 13 = Z_to_bv 64 480 -> getr regs 15 = Z_to_bv 64 18446744073709551615 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 15 + 4) (art_ic_mc 15)) (ca + 80 * 15 + 8) (art_ic_size 15)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 1288) /\ getr regs' 13 = Z_to_bv 64 512 /\ getr regs' 15 = Z_to_bv 64 0
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 15 + 4) (art_ic_mc 15) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 15 + 8) (art_ic_size 15) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_16 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 1288) -> getr regs 13 = Z_to_bv 64 512 -> getr regs 15 = Z_to_bv 64 0 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 16 + 4) (art_ic_mc 16)) (ca + 80 * 16 + 8) (art_ic_size 16)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 1368) /\ getr regs' 13 = Z_to_bv 64 544 /\ getr regs' 15 = Z_to_bv 64 1
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbtk F_57124 D_57124.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 16 + 4) (art_ic_mc 16) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 16 + 8) (art_ic_size 16) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_17 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 1368) -> getr regs 13 = Z_to_bv 64 544 -> getr regs 15 = Z_to_bv 64 1 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 17 + 4) (art_ic_mc 17)) (ca + 80 * 17 + 8) (art_ic_size 17)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 1448) /\ getr regs' 13 = Z_to_bv 64 576 /\ getr regs' 15 = Z_to_bv 64 2
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 17 + 4) (art_ic_mc 17) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 17 + 8) (art_ic_size 17) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_18 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 1448) -> getr regs 13 = Z_to_bv 64 576 -> getr regs 15 = Z_to_bv 64 2 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 18 + 4) (art_ic_mc 18)) (ca + 80 * 18 + 8) (art_ic_size 18)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 1528) /\ getr regs' 13 = Z_to_bv 64 608 /\ getr regs' 15 = Z_to_bv 64 3
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 18 + 4) (art_ic_mc 18) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 18 + 8) (art_ic_size 18) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_19 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 1528) -> getr regs 13 = Z_to_bv 64 608 -> getr regs 15 = Z_to_bv 64 3 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 19 + 4) (art_ic_mc 19)) (ca + 80 * 19 + 8) (art_ic_size 19)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 1608) /\ getr regs' 13 = Z_to_bv 64 640 /\ getr regs' 15 = Z_to_bv 64 4
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 19 + 4) (art_ic_mc 19) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 19 + 8) (art_ic_size 19) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_20 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 1608) -> getr regs 13 = Z_to_bv 64 640 -> getr regs 15 = Z_to_bv 64 4 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 20 + 4) (art_ic_mc 20)) (ca + 80 * 20 + 8) (art_ic_size 20)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 1688) /\ getr regs' 13 = Z_to_bv 64 672 /\ getr regs' 15 = Z_to_bv 64 5
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 20 + 4) (art_ic_mc 20) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 20 + 8) (art_ic_size 20) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_21 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 1688) -> getr regs 13 = Z_to_bv 64 672 -> getr regs 15 = Z_to_bv 64 5 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 21 + 4) (art_ic_mc 21)) (ca + 80 * 21 + 8) (art_ic_size 21)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 1768) /\ getr regs' 13 = Z_to_bv 64 704 /\ getr regs' 15 = Z_to_bv 64 6
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 21 + 4) (art_ic_mc 21) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 21 + 8) (art_ic_size 21) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_22 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 1768) -> getr regs 13 = Z_to_bv 64 704 -> getr regs 15 = Z_to_bv 64 6 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 22 + 4) (art_ic_mc 22)) (ca + 80 * 22 + 8) (art_ic_size 22)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 1848) /\ getr regs' 13 = Z_to_bv 64 736 /\ getr regs' 15 = Z_to_bv 64 7
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 22 + 4) (art_ic_mc 22) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 22 + 8) (art_ic_size 22) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_23 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 1848) -> getr regs 13 = Z_to_bv 64 736 -> getr regs 15 = Z_to_bv 64 7 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 23 + 4) (art_ic_mc 23)) (ca + 80 * 23 + 8) (art_ic_size 23)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 1928) /\ getr regs' 13 = Z_to_bv 64 768 /\ getr regs' 15 = Z_to_bv 64 8
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 23 + 4) (art_ic_mc 23) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 23 + 8) (art_ic_size 23) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_24 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 1928) -> getr regs 13 = Z_to_bv 64 768 -> getr regs 15 = Z_to_bv 64 8 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 24 + 4) (art_ic_mc 24)) (ca + 80 * 24 + 8) (art_ic_size 24)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 2008) /\ getr regs' 13 = Z_to_bv 64 800 /\ getr regs' 15 = Z_to_bv 64 9
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 24 + 4) (art_ic_mc 24) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 24 + 8) (art_ic_size 24) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_25 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 2008) -> getr regs 13 = Z_to_bv 64 800 -> getr regs 15 = Z_to_bv 64 9 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 25 + 4) (art_ic_mc 25)) (ca + 80 * 25 + 8) (art_ic_size 25)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 2088) /\ getr regs' 13 = Z_to_bv 64 832 /\ getr regs' 15 = Z_to_bv 64 10
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 25 + 4) (art_ic_mc 25) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 25 + 8) (art_ic_size 25) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_26 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 2088) -> getr regs 13 = Z_to_bv 64 832 -> getr regs 15 = Z_to_bv 64 10 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 26 + 4) (art_ic_mc 26)) (ca + 80 * 26 + 8) (art_ic_size 26)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 2168) /\ getr regs' 13 = Z_to_bv 64 864 /\ getr regs' 15 = Z_to_bv 64 11
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 26 + 4) (art_ic_mc 26) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 26 + 8) (art_ic_size 26) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_27 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 2168) -> getr regs 13 = Z_to_bv 64 864 -> getr regs 15 = Z_to_bv 64 11 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 27 + 4) (art_ic_mc 27)) (ca + 80 * 27 + 8) (art_ic_size 27)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 2248) /\ getr regs' 13 = Z_to_bv 64 896 /\ getr regs' 15 = Z_to_bv 64 12
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 27 + 4) (art_ic_mc 27) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 27 + 8) (art_ic_size 27) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_28 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 2248) -> getr regs 13 = Z_to_bv 64 896 -> getr regs 15 = Z_to_bv 64 12 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 28 + 4) (art_ic_mc 28)) (ca + 80 * 28 + 8) (art_ic_size 28)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 2328) /\ getr regs' 13 = Z_to_bv 64 928 /\ getr regs' 15 = Z_to_bv 64 13
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 28 + 4) (art_ic_mc 28) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 28 + 8) (art_ic_size 28) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_29 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 2328) -> getr regs 13 = Z_to_bv 64 928 -> getr regs 15 = Z_to_bv 64 13 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 29 + 4) (art_ic_mc 29)) (ca + 80 * 29 + 8) (art_ic_size 29)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 2408) /\ getr regs' 13 = Z_to_bv 64 960 /\ getr regs' 15 = Z_to_bv 64 14
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 29 + 4) (art_ic_mc 29) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 29 + 8) (art_ic_size 29) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_30 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 2408) -> getr regs 13 = Z_to_bv 64 960 -> getr regs 15 = Z_to_bv 64 14 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57530 : word) (Wn 8 (Wn 4 M (ca + 80 * 30 + 4) (art_ic_mc 30)) (ca + 80 * 30 + 8) (art_ic_size 30)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 2488) /\ getr regs' 13 = Z_to_bv 64 992 /\ getr regs' 15 = Z_to_bv 64 15
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbft F_57118 D_57118.
    zstep F_5711c D_5711c.
    zstep F_57120 D_57120.
    zbft F_57124 D_57124.
    zstep F_57128 D_57128.
    zstep F_5712c D_5712c.
    zstep F_57130 D_57130.
    zstep F_57134 D_57134.
    zstep F_57138 D_57138.
    zstep F_5713c D_5713c.
    zstep F_57140 D_57140.
    zstep F_57144 D_57144.
    zstep F_57148 D_57148.
    zbtk F_5714c D_5714c.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 30 + 4) (art_ic_mc 30) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 30 + 8) (art_ic_size 30) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbft F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_it_31 : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 2488) -> getr regs 13 = Z_to_bv 64 992 -> getr regs 15 = Z_to_bv 64 15 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57584 : word) (Wn 8 (Wn 4 M (ca + 80 * 31 + 4) (art_ic_mc 31)) (ca + 80 * 31 + 8) (art_ic_size 31)) rom)
    /\ getr regs' 11 = Z_to_bv 64 (ca + 2568) /\ getr regs' 13 = Z_to_bv 64 1024 /\ getr regs' 15 = Z_to_bv 64 16
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca H11 H13 H15 H16 H17 H5 H6 H7 Hca Hca' W.
  eexists. split.
  { zbtk F_57118 D_57118.
    zstep F_57158 D_57158.
    zstep F_5715c D_5715c.
    zstep F_57160 D_57160.
    zbft F_57164 D_57164.
    stepn F_57168 D_57168.
    zstep F_57150 D_57150.
    stepn F_57154 D_57154.
    zstep F_570f4 D_570f4.
    zstep F_570f8 D_570f8.
    zstep F_570fc D_570fc.
    zstep F_57100 D_57100.
    zstep F_57104 D_57104.
    zsw F_57108 D_57108 (ca + 80 * 31 + 4) (art_ic_mc 31) ltac:(rewok W).
    zsd F_5710c D_5710c (ca + 80 * 31 + 8) (art_ic_size 31) ltac:(rewok W).
    zstep F_57110 D_57110.
    zbtk F_57114 D_57114.
    first [apply mst_refl | apply art_msteps_of_eq; apply art_mkst_eq; [reflexivity | zval | reflexivity]]. }
  split; [kept_solve|]. split; [kept_solve|]. split; [kept_solve|].
  intros r Hr. unfold art_ic_kept in Hr. decompose [and] Hr. kept_solve.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_ic_loop : forall regs (M rom : word -> option byte) (ca : Z),
  getr regs 11 = Z_to_bv 64 (ca + 88) -> getr regs 13 = Z_to_bv 64 32 -> getr regs 15 = Z_to_bv 64 18446744073709551601 ->
  getr regs 16 = Z_to_bv 64 15 -> getr regs 17 = Z_to_bv 64 1024 -> getr regs 5 = Z_to_bv 64 16 -> getr regs 6 = Z_to_bv 64 17 -> getr regs 7 = Z_to_bv 64 512 ->
  4096 <= ca -> ca + 4096 < 2 ^ 64 -> wrA M ca 2592 ->
  exists regs',
    msteps ASEGS (mkst regs (0x57530 : word) M rom) (mkst regs' (0x57584 : word) (art_ic_mem M ca 31) rom)
    /\ (forall r : reg, art_ic_kept r -> getr regs' r = getr regs r).
Proof.
  intros regs M rom ca A0 B0 C0 H16_0 H17_0 H5_0 H6_0 H7_0 Hca Hca' W0.
  #[local] Ltac ick := unfold art_ic_kept; repeat split; intros E; discriminate E.
  destruct (art_ic_it_1 regs M rom ca A0 B0 C0 H16_0 H17_0 H5_0 H6_0 H7_0 Hca Hca' W0) as (r1 & RUN1 & A1 & B1 & C1 & K1).
  match type of RUN1 with msteps _ _ (mkst _ _ ?X _) => set (M1 := X) in RUN1 end.
  assert (W1 : wrA M1 ca 2592) by (unfold M1; do 2 apply wr_Wn; exact W0).
  assert (H16_1 : getr r1 16 = Z_to_bv 64 15) by (rewrite (K1 16%bv) by ick; exact H16_0). assert (H17_1 : getr r1 17 = Z_to_bv 64 1024) by (rewrite (K1 17%bv) by ick; exact H17_0).
  assert (H5_1 : getr r1 5 = Z_to_bv 64 16) by (rewrite (K1 5%bv) by ick; exact H5_0). assert (H6_1 : getr r1 6 = Z_to_bv 64 17) by (rewrite (K1 6%bv) by ick; exact H6_0). assert (H7_1 : getr r1 7 = Z_to_bv 64 512) by (rewrite (K1 7%bv) by ick; exact H7_0).
  clear A0 B0 C0 H16_0 H17_0 H5_0 H6_0 H7_0 W0.
  destruct (art_ic_it_2 r1 M1 rom ca A1 B1 C1 H16_1 H17_1 H5_1 H6_1 H7_1 Hca Hca' W1) as (r2 & RUN2 & A2 & B2 & C2 & K2).
  match type of RUN2 with msteps _ _ (mkst _ _ ?X _) => set (M2 := X) in RUN2 end.
  assert (W2 : wrA M2 ca 2592) by (unfold M2; do 2 apply wr_Wn; exact W1).
  assert (H16_2 : getr r2 16 = Z_to_bv 64 15) by (rewrite (K2 16%bv) by ick; exact H16_1). assert (H17_2 : getr r2 17 = Z_to_bv 64 1024) by (rewrite (K2 17%bv) by ick; exact H17_1).
  assert (H5_2 : getr r2 5 = Z_to_bv 64 16) by (rewrite (K2 5%bv) by ick; exact H5_1). assert (H6_2 : getr r2 6 = Z_to_bv 64 17) by (rewrite (K2 6%bv) by ick; exact H6_1). assert (H7_2 : getr r2 7 = Z_to_bv 64 512) by (rewrite (K2 7%bv) by ick; exact H7_1).
  clear A1 B1 C1 H16_1 H17_1 H5_1 H6_1 H7_1 W1.
  destruct (art_ic_it_3 r2 M2 rom ca A2 B2 C2 H16_2 H17_2 H5_2 H6_2 H7_2 Hca Hca' W2) as (r3 & RUN3 & A3 & B3 & C3 & K3).
  match type of RUN3 with msteps _ _ (mkst _ _ ?X _) => set (M3 := X) in RUN3 end.
  assert (W3 : wrA M3 ca 2592) by (unfold M3; do 2 apply wr_Wn; exact W2).
  assert (H16_3 : getr r3 16 = Z_to_bv 64 15) by (rewrite (K3 16%bv) by ick; exact H16_2). assert (H17_3 : getr r3 17 = Z_to_bv 64 1024) by (rewrite (K3 17%bv) by ick; exact H17_2).
  assert (H5_3 : getr r3 5 = Z_to_bv 64 16) by (rewrite (K3 5%bv) by ick; exact H5_2). assert (H6_3 : getr r3 6 = Z_to_bv 64 17) by (rewrite (K3 6%bv) by ick; exact H6_2). assert (H7_3 : getr r3 7 = Z_to_bv 64 512) by (rewrite (K3 7%bv) by ick; exact H7_2).
  clear A2 B2 C2 H16_2 H17_2 H5_2 H6_2 H7_2 W2.
  destruct (art_ic_it_4 r3 M3 rom ca A3 B3 C3 H16_3 H17_3 H5_3 H6_3 H7_3 Hca Hca' W3) as (r4 & RUN4 & A4 & B4 & C4 & K4).
  match type of RUN4 with msteps _ _ (mkst _ _ ?X _) => set (M4 := X) in RUN4 end.
  assert (W4 : wrA M4 ca 2592) by (unfold M4; do 2 apply wr_Wn; exact W3).
  assert (H16_4 : getr r4 16 = Z_to_bv 64 15) by (rewrite (K4 16%bv) by ick; exact H16_3). assert (H17_4 : getr r4 17 = Z_to_bv 64 1024) by (rewrite (K4 17%bv) by ick; exact H17_3).
  assert (H5_4 : getr r4 5 = Z_to_bv 64 16) by (rewrite (K4 5%bv) by ick; exact H5_3). assert (H6_4 : getr r4 6 = Z_to_bv 64 17) by (rewrite (K4 6%bv) by ick; exact H6_3). assert (H7_4 : getr r4 7 = Z_to_bv 64 512) by (rewrite (K4 7%bv) by ick; exact H7_3).
  clear A3 B3 C3 H16_3 H17_3 H5_3 H6_3 H7_3 W3.
  destruct (art_ic_it_5 r4 M4 rom ca A4 B4 C4 H16_4 H17_4 H5_4 H6_4 H7_4 Hca Hca' W4) as (r5 & RUN5 & A5 & B5 & C5 & K5).
  match type of RUN5 with msteps _ _ (mkst _ _ ?X _) => set (M5 := X) in RUN5 end.
  assert (W5 : wrA M5 ca 2592) by (unfold M5; do 2 apply wr_Wn; exact W4).
  assert (H16_5 : getr r5 16 = Z_to_bv 64 15) by (rewrite (K5 16%bv) by ick; exact H16_4). assert (H17_5 : getr r5 17 = Z_to_bv 64 1024) by (rewrite (K5 17%bv) by ick; exact H17_4).
  assert (H5_5 : getr r5 5 = Z_to_bv 64 16) by (rewrite (K5 5%bv) by ick; exact H5_4). assert (H6_5 : getr r5 6 = Z_to_bv 64 17) by (rewrite (K5 6%bv) by ick; exact H6_4). assert (H7_5 : getr r5 7 = Z_to_bv 64 512) by (rewrite (K5 7%bv) by ick; exact H7_4).
  clear A4 B4 C4 H16_4 H17_4 H5_4 H6_4 H7_4 W4.
  destruct (art_ic_it_6 r5 M5 rom ca A5 B5 C5 H16_5 H17_5 H5_5 H6_5 H7_5 Hca Hca' W5) as (r6 & RUN6 & A6 & B6 & C6 & K6).
  match type of RUN6 with msteps _ _ (mkst _ _ ?X _) => set (M6 := X) in RUN6 end.
  assert (W6 : wrA M6 ca 2592) by (unfold M6; do 2 apply wr_Wn; exact W5).
  assert (H16_6 : getr r6 16 = Z_to_bv 64 15) by (rewrite (K6 16%bv) by ick; exact H16_5). assert (H17_6 : getr r6 17 = Z_to_bv 64 1024) by (rewrite (K6 17%bv) by ick; exact H17_5).
  assert (H5_6 : getr r6 5 = Z_to_bv 64 16) by (rewrite (K6 5%bv) by ick; exact H5_5). assert (H6_6 : getr r6 6 = Z_to_bv 64 17) by (rewrite (K6 6%bv) by ick; exact H6_5). assert (H7_6 : getr r6 7 = Z_to_bv 64 512) by (rewrite (K6 7%bv) by ick; exact H7_5).
  clear A5 B5 C5 H16_5 H17_5 H5_5 H6_5 H7_5 W5.
  destruct (art_ic_it_7 r6 M6 rom ca A6 B6 C6 H16_6 H17_6 H5_6 H6_6 H7_6 Hca Hca' W6) as (r7 & RUN7 & A7 & B7 & C7 & K7).
  match type of RUN7 with msteps _ _ (mkst _ _ ?X _) => set (M7 := X) in RUN7 end.
  assert (W7 : wrA M7 ca 2592) by (unfold M7; do 2 apply wr_Wn; exact W6).
  assert (H16_7 : getr r7 16 = Z_to_bv 64 15) by (rewrite (K7 16%bv) by ick; exact H16_6). assert (H17_7 : getr r7 17 = Z_to_bv 64 1024) by (rewrite (K7 17%bv) by ick; exact H17_6).
  assert (H5_7 : getr r7 5 = Z_to_bv 64 16) by (rewrite (K7 5%bv) by ick; exact H5_6). assert (H6_7 : getr r7 6 = Z_to_bv 64 17) by (rewrite (K7 6%bv) by ick; exact H6_6). assert (H7_7 : getr r7 7 = Z_to_bv 64 512) by (rewrite (K7 7%bv) by ick; exact H7_6).
  clear A6 B6 C6 H16_6 H17_6 H5_6 H6_6 H7_6 W6.
  destruct (art_ic_it_8 r7 M7 rom ca A7 B7 C7 H16_7 H17_7 H5_7 H6_7 H7_7 Hca Hca' W7) as (r8 & RUN8 & A8 & B8 & C8 & K8).
  match type of RUN8 with msteps _ _ (mkst _ _ ?X _) => set (M8 := X) in RUN8 end.
  assert (W8 : wrA M8 ca 2592) by (unfold M8; do 2 apply wr_Wn; exact W7).
  assert (H16_8 : getr r8 16 = Z_to_bv 64 15) by (rewrite (K8 16%bv) by ick; exact H16_7). assert (H17_8 : getr r8 17 = Z_to_bv 64 1024) by (rewrite (K8 17%bv) by ick; exact H17_7).
  assert (H5_8 : getr r8 5 = Z_to_bv 64 16) by (rewrite (K8 5%bv) by ick; exact H5_7). assert (H6_8 : getr r8 6 = Z_to_bv 64 17) by (rewrite (K8 6%bv) by ick; exact H6_7). assert (H7_8 : getr r8 7 = Z_to_bv 64 512) by (rewrite (K8 7%bv) by ick; exact H7_7).
  clear A7 B7 C7 H16_7 H17_7 H5_7 H6_7 H7_7 W7.
  destruct (art_ic_it_9 r8 M8 rom ca A8 B8 C8 H16_8 H17_8 H5_8 H6_8 H7_8 Hca Hca' W8) as (r9 & RUN9 & A9 & B9 & C9 & K9).
  match type of RUN9 with msteps _ _ (mkst _ _ ?X _) => set (M9 := X) in RUN9 end.
  assert (W9 : wrA M9 ca 2592) by (unfold M9; do 2 apply wr_Wn; exact W8).
  assert (H16_9 : getr r9 16 = Z_to_bv 64 15) by (rewrite (K9 16%bv) by ick; exact H16_8). assert (H17_9 : getr r9 17 = Z_to_bv 64 1024) by (rewrite (K9 17%bv) by ick; exact H17_8).
  assert (H5_9 : getr r9 5 = Z_to_bv 64 16) by (rewrite (K9 5%bv) by ick; exact H5_8). assert (H6_9 : getr r9 6 = Z_to_bv 64 17) by (rewrite (K9 6%bv) by ick; exact H6_8). assert (H7_9 : getr r9 7 = Z_to_bv 64 512) by (rewrite (K9 7%bv) by ick; exact H7_8).
  clear A8 B8 C8 H16_8 H17_8 H5_8 H6_8 H7_8 W8.
  destruct (art_ic_it_10 r9 M9 rom ca A9 B9 C9 H16_9 H17_9 H5_9 H6_9 H7_9 Hca Hca' W9) as (r10 & RUN10 & A10 & B10 & C10 & K10).
  match type of RUN10 with msteps _ _ (mkst _ _ ?X _) => set (M10 := X) in RUN10 end.
  assert (W10 : wrA M10 ca 2592) by (unfold M10; do 2 apply wr_Wn; exact W9).
  assert (H16_10 : getr r10 16 = Z_to_bv 64 15) by (rewrite (K10 16%bv) by ick; exact H16_9). assert (H17_10 : getr r10 17 = Z_to_bv 64 1024) by (rewrite (K10 17%bv) by ick; exact H17_9).
  assert (H5_10 : getr r10 5 = Z_to_bv 64 16) by (rewrite (K10 5%bv) by ick; exact H5_9). assert (H6_10 : getr r10 6 = Z_to_bv 64 17) by (rewrite (K10 6%bv) by ick; exact H6_9). assert (H7_10 : getr r10 7 = Z_to_bv 64 512) by (rewrite (K10 7%bv) by ick; exact H7_9).
  clear A9 B9 C9 H16_9 H17_9 H5_9 H6_9 H7_9 W9.
  destruct (art_ic_it_11 r10 M10 rom ca A10 B10 C10 H16_10 H17_10 H5_10 H6_10 H7_10 Hca Hca' W10) as (r11 & RUN11 & A11 & B11 & C11 & K11).
  match type of RUN11 with msteps _ _ (mkst _ _ ?X _) => set (M11 := X) in RUN11 end.
  assert (W11 : wrA M11 ca 2592) by (unfold M11; do 2 apply wr_Wn; exact W10).
  assert (H16_11 : getr r11 16 = Z_to_bv 64 15) by (rewrite (K11 16%bv) by ick; exact H16_10). assert (H17_11 : getr r11 17 = Z_to_bv 64 1024) by (rewrite (K11 17%bv) by ick; exact H17_10).
  assert (H5_11 : getr r11 5 = Z_to_bv 64 16) by (rewrite (K11 5%bv) by ick; exact H5_10). assert (H6_11 : getr r11 6 = Z_to_bv 64 17) by (rewrite (K11 6%bv) by ick; exact H6_10). assert (H7_11 : getr r11 7 = Z_to_bv 64 512) by (rewrite (K11 7%bv) by ick; exact H7_10).
  clear A10 B10 C10 H16_10 H17_10 H5_10 H6_10 H7_10 W10.
  destruct (art_ic_it_12 r11 M11 rom ca A11 B11 C11 H16_11 H17_11 H5_11 H6_11 H7_11 Hca Hca' W11) as (r12 & RUN12 & A12 & B12 & C12 & K12).
  match type of RUN12 with msteps _ _ (mkst _ _ ?X _) => set (M12 := X) in RUN12 end.
  assert (W12 : wrA M12 ca 2592) by (unfold M12; do 2 apply wr_Wn; exact W11).
  assert (H16_12 : getr r12 16 = Z_to_bv 64 15) by (rewrite (K12 16%bv) by ick; exact H16_11). assert (H17_12 : getr r12 17 = Z_to_bv 64 1024) by (rewrite (K12 17%bv) by ick; exact H17_11).
  assert (H5_12 : getr r12 5 = Z_to_bv 64 16) by (rewrite (K12 5%bv) by ick; exact H5_11). assert (H6_12 : getr r12 6 = Z_to_bv 64 17) by (rewrite (K12 6%bv) by ick; exact H6_11). assert (H7_12 : getr r12 7 = Z_to_bv 64 512) by (rewrite (K12 7%bv) by ick; exact H7_11).
  clear A11 B11 C11 H16_11 H17_11 H5_11 H6_11 H7_11 W11.
  destruct (art_ic_it_13 r12 M12 rom ca A12 B12 C12 H16_12 H17_12 H5_12 H6_12 H7_12 Hca Hca' W12) as (r13 & RUN13 & A13 & B13 & C13 & K13).
  match type of RUN13 with msteps _ _ (mkst _ _ ?X _) => set (M13 := X) in RUN13 end.
  assert (W13 : wrA M13 ca 2592) by (unfold M13; do 2 apply wr_Wn; exact W12).
  assert (H16_13 : getr r13 16 = Z_to_bv 64 15) by (rewrite (K13 16%bv) by ick; exact H16_12). assert (H17_13 : getr r13 17 = Z_to_bv 64 1024) by (rewrite (K13 17%bv) by ick; exact H17_12).
  assert (H5_13 : getr r13 5 = Z_to_bv 64 16) by (rewrite (K13 5%bv) by ick; exact H5_12). assert (H6_13 : getr r13 6 = Z_to_bv 64 17) by (rewrite (K13 6%bv) by ick; exact H6_12). assert (H7_13 : getr r13 7 = Z_to_bv 64 512) by (rewrite (K13 7%bv) by ick; exact H7_12).
  clear A12 B12 C12 H16_12 H17_12 H5_12 H6_12 H7_12 W12.
  destruct (art_ic_it_14 r13 M13 rom ca A13 B13 C13 H16_13 H17_13 H5_13 H6_13 H7_13 Hca Hca' W13) as (r14 & RUN14 & A14 & B14 & C14 & K14).
  match type of RUN14 with msteps _ _ (mkst _ _ ?X _) => set (M14 := X) in RUN14 end.
  assert (W14 : wrA M14 ca 2592) by (unfold M14; do 2 apply wr_Wn; exact W13).
  assert (H16_14 : getr r14 16 = Z_to_bv 64 15) by (rewrite (K14 16%bv) by ick; exact H16_13). assert (H17_14 : getr r14 17 = Z_to_bv 64 1024) by (rewrite (K14 17%bv) by ick; exact H17_13).
  assert (H5_14 : getr r14 5 = Z_to_bv 64 16) by (rewrite (K14 5%bv) by ick; exact H5_13). assert (H6_14 : getr r14 6 = Z_to_bv 64 17) by (rewrite (K14 6%bv) by ick; exact H6_13). assert (H7_14 : getr r14 7 = Z_to_bv 64 512) by (rewrite (K14 7%bv) by ick; exact H7_13).
  clear A13 B13 C13 H16_13 H17_13 H5_13 H6_13 H7_13 W13.
  destruct (art_ic_it_15 r14 M14 rom ca A14 B14 C14 H16_14 H17_14 H5_14 H6_14 H7_14 Hca Hca' W14) as (r15 & RUN15 & A15 & B15 & C15 & K15).
  match type of RUN15 with msteps _ _ (mkst _ _ ?X _) => set (M15 := X) in RUN15 end.
  assert (W15 : wrA M15 ca 2592) by (unfold M15; do 2 apply wr_Wn; exact W14).
  assert (H16_15 : getr r15 16 = Z_to_bv 64 15) by (rewrite (K15 16%bv) by ick; exact H16_14). assert (H17_15 : getr r15 17 = Z_to_bv 64 1024) by (rewrite (K15 17%bv) by ick; exact H17_14).
  assert (H5_15 : getr r15 5 = Z_to_bv 64 16) by (rewrite (K15 5%bv) by ick; exact H5_14). assert (H6_15 : getr r15 6 = Z_to_bv 64 17) by (rewrite (K15 6%bv) by ick; exact H6_14). assert (H7_15 : getr r15 7 = Z_to_bv 64 512) by (rewrite (K15 7%bv) by ick; exact H7_14).
  clear A14 B14 C14 H16_14 H17_14 H5_14 H6_14 H7_14 W14.
  destruct (art_ic_it_16 r15 M15 rom ca A15 B15 C15 H16_15 H17_15 H5_15 H6_15 H7_15 Hca Hca' W15) as (r16 & RUN16 & A16 & B16 & C16 & K16).
  match type of RUN16 with msteps _ _ (mkst _ _ ?X _) => set (M16 := X) in RUN16 end.
  assert (W16 : wrA M16 ca 2592) by (unfold M16; do 2 apply wr_Wn; exact W15).
  assert (H16_16 : getr r16 16 = Z_to_bv 64 15) by (rewrite (K16 16%bv) by ick; exact H16_15). assert (H17_16 : getr r16 17 = Z_to_bv 64 1024) by (rewrite (K16 17%bv) by ick; exact H17_15).
  assert (H5_16 : getr r16 5 = Z_to_bv 64 16) by (rewrite (K16 5%bv) by ick; exact H5_15). assert (H6_16 : getr r16 6 = Z_to_bv 64 17) by (rewrite (K16 6%bv) by ick; exact H6_15). assert (H7_16 : getr r16 7 = Z_to_bv 64 512) by (rewrite (K16 7%bv) by ick; exact H7_15).
  clear A15 B15 C15 H16_15 H17_15 H5_15 H6_15 H7_15 W15.
  destruct (art_ic_it_17 r16 M16 rom ca A16 B16 C16 H16_16 H17_16 H5_16 H6_16 H7_16 Hca Hca' W16) as (r17 & RUN17 & A17 & B17 & C17 & K17).
  match type of RUN17 with msteps _ _ (mkst _ _ ?X _) => set (M17 := X) in RUN17 end.
  assert (W17 : wrA M17 ca 2592) by (unfold M17; do 2 apply wr_Wn; exact W16).
  assert (H16_17 : getr r17 16 = Z_to_bv 64 15) by (rewrite (K17 16%bv) by ick; exact H16_16). assert (H17_17 : getr r17 17 = Z_to_bv 64 1024) by (rewrite (K17 17%bv) by ick; exact H17_16).
  assert (H5_17 : getr r17 5 = Z_to_bv 64 16) by (rewrite (K17 5%bv) by ick; exact H5_16). assert (H6_17 : getr r17 6 = Z_to_bv 64 17) by (rewrite (K17 6%bv) by ick; exact H6_16). assert (H7_17 : getr r17 7 = Z_to_bv 64 512) by (rewrite (K17 7%bv) by ick; exact H7_16).
  clear A16 B16 C16 H16_16 H17_16 H5_16 H6_16 H7_16 W16.
  destruct (art_ic_it_18 r17 M17 rom ca A17 B17 C17 H16_17 H17_17 H5_17 H6_17 H7_17 Hca Hca' W17) as (r18 & RUN18 & A18 & B18 & C18 & K18).
  match type of RUN18 with msteps _ _ (mkst _ _ ?X _) => set (M18 := X) in RUN18 end.
  assert (W18 : wrA M18 ca 2592) by (unfold M18; do 2 apply wr_Wn; exact W17).
  assert (H16_18 : getr r18 16 = Z_to_bv 64 15) by (rewrite (K18 16%bv) by ick; exact H16_17). assert (H17_18 : getr r18 17 = Z_to_bv 64 1024) by (rewrite (K18 17%bv) by ick; exact H17_17).
  assert (H5_18 : getr r18 5 = Z_to_bv 64 16) by (rewrite (K18 5%bv) by ick; exact H5_17). assert (H6_18 : getr r18 6 = Z_to_bv 64 17) by (rewrite (K18 6%bv) by ick; exact H6_17). assert (H7_18 : getr r18 7 = Z_to_bv 64 512) by (rewrite (K18 7%bv) by ick; exact H7_17).
  clear A17 B17 C17 H16_17 H17_17 H5_17 H6_17 H7_17 W17.
  destruct (art_ic_it_19 r18 M18 rom ca A18 B18 C18 H16_18 H17_18 H5_18 H6_18 H7_18 Hca Hca' W18) as (r19 & RUN19 & A19 & B19 & C19 & K19).
  match type of RUN19 with msteps _ _ (mkst _ _ ?X _) => set (M19 := X) in RUN19 end.
  assert (W19 : wrA M19 ca 2592) by (unfold M19; do 2 apply wr_Wn; exact W18).
  assert (H16_19 : getr r19 16 = Z_to_bv 64 15) by (rewrite (K19 16%bv) by ick; exact H16_18). assert (H17_19 : getr r19 17 = Z_to_bv 64 1024) by (rewrite (K19 17%bv) by ick; exact H17_18).
  assert (H5_19 : getr r19 5 = Z_to_bv 64 16) by (rewrite (K19 5%bv) by ick; exact H5_18). assert (H6_19 : getr r19 6 = Z_to_bv 64 17) by (rewrite (K19 6%bv) by ick; exact H6_18). assert (H7_19 : getr r19 7 = Z_to_bv 64 512) by (rewrite (K19 7%bv) by ick; exact H7_18).
  clear A18 B18 C18 H16_18 H17_18 H5_18 H6_18 H7_18 W18.
  destruct (art_ic_it_20 r19 M19 rom ca A19 B19 C19 H16_19 H17_19 H5_19 H6_19 H7_19 Hca Hca' W19) as (r20 & RUN20 & A20 & B20 & C20 & K20).
  match type of RUN20 with msteps _ _ (mkst _ _ ?X _) => set (M20 := X) in RUN20 end.
  assert (W20 : wrA M20 ca 2592) by (unfold M20; do 2 apply wr_Wn; exact W19).
  assert (H16_20 : getr r20 16 = Z_to_bv 64 15) by (rewrite (K20 16%bv) by ick; exact H16_19). assert (H17_20 : getr r20 17 = Z_to_bv 64 1024) by (rewrite (K20 17%bv) by ick; exact H17_19).
  assert (H5_20 : getr r20 5 = Z_to_bv 64 16) by (rewrite (K20 5%bv) by ick; exact H5_19). assert (H6_20 : getr r20 6 = Z_to_bv 64 17) by (rewrite (K20 6%bv) by ick; exact H6_19). assert (H7_20 : getr r20 7 = Z_to_bv 64 512) by (rewrite (K20 7%bv) by ick; exact H7_19).
  clear A19 B19 C19 H16_19 H17_19 H5_19 H6_19 H7_19 W19.
  destruct (art_ic_it_21 r20 M20 rom ca A20 B20 C20 H16_20 H17_20 H5_20 H6_20 H7_20 Hca Hca' W20) as (r21 & RUN21 & A21 & B21 & C21 & K21).
  match type of RUN21 with msteps _ _ (mkst _ _ ?X _) => set (M21 := X) in RUN21 end.
  assert (W21 : wrA M21 ca 2592) by (unfold M21; do 2 apply wr_Wn; exact W20).
  assert (H16_21 : getr r21 16 = Z_to_bv 64 15) by (rewrite (K21 16%bv) by ick; exact H16_20). assert (H17_21 : getr r21 17 = Z_to_bv 64 1024) by (rewrite (K21 17%bv) by ick; exact H17_20).
  assert (H5_21 : getr r21 5 = Z_to_bv 64 16) by (rewrite (K21 5%bv) by ick; exact H5_20). assert (H6_21 : getr r21 6 = Z_to_bv 64 17) by (rewrite (K21 6%bv) by ick; exact H6_20). assert (H7_21 : getr r21 7 = Z_to_bv 64 512) by (rewrite (K21 7%bv) by ick; exact H7_20).
  clear A20 B20 C20 H16_20 H17_20 H5_20 H6_20 H7_20 W20.
  destruct (art_ic_it_22 r21 M21 rom ca A21 B21 C21 H16_21 H17_21 H5_21 H6_21 H7_21 Hca Hca' W21) as (r22 & RUN22 & A22 & B22 & C22 & K22).
  match type of RUN22 with msteps _ _ (mkst _ _ ?X _) => set (M22 := X) in RUN22 end.
  assert (W22 : wrA M22 ca 2592) by (unfold M22; do 2 apply wr_Wn; exact W21).
  assert (H16_22 : getr r22 16 = Z_to_bv 64 15) by (rewrite (K22 16%bv) by ick; exact H16_21). assert (H17_22 : getr r22 17 = Z_to_bv 64 1024) by (rewrite (K22 17%bv) by ick; exact H17_21).
  assert (H5_22 : getr r22 5 = Z_to_bv 64 16) by (rewrite (K22 5%bv) by ick; exact H5_21). assert (H6_22 : getr r22 6 = Z_to_bv 64 17) by (rewrite (K22 6%bv) by ick; exact H6_21). assert (H7_22 : getr r22 7 = Z_to_bv 64 512) by (rewrite (K22 7%bv) by ick; exact H7_21).
  clear A21 B21 C21 H16_21 H17_21 H5_21 H6_21 H7_21 W21.
  destruct (art_ic_it_23 r22 M22 rom ca A22 B22 C22 H16_22 H17_22 H5_22 H6_22 H7_22 Hca Hca' W22) as (r23 & RUN23 & A23 & B23 & C23 & K23).
  match type of RUN23 with msteps _ _ (mkst _ _ ?X _) => set (M23 := X) in RUN23 end.
  assert (W23 : wrA M23 ca 2592) by (unfold M23; do 2 apply wr_Wn; exact W22).
  assert (H16_23 : getr r23 16 = Z_to_bv 64 15) by (rewrite (K23 16%bv) by ick; exact H16_22). assert (H17_23 : getr r23 17 = Z_to_bv 64 1024) by (rewrite (K23 17%bv) by ick; exact H17_22).
  assert (H5_23 : getr r23 5 = Z_to_bv 64 16) by (rewrite (K23 5%bv) by ick; exact H5_22). assert (H6_23 : getr r23 6 = Z_to_bv 64 17) by (rewrite (K23 6%bv) by ick; exact H6_22). assert (H7_23 : getr r23 7 = Z_to_bv 64 512) by (rewrite (K23 7%bv) by ick; exact H7_22).
  clear A22 B22 C22 H16_22 H17_22 H5_22 H6_22 H7_22 W22.
  destruct (art_ic_it_24 r23 M23 rom ca A23 B23 C23 H16_23 H17_23 H5_23 H6_23 H7_23 Hca Hca' W23) as (r24 & RUN24 & A24 & B24 & C24 & K24).
  match type of RUN24 with msteps _ _ (mkst _ _ ?X _) => set (M24 := X) in RUN24 end.
  assert (W24 : wrA M24 ca 2592) by (unfold M24; do 2 apply wr_Wn; exact W23).
  assert (H16_24 : getr r24 16 = Z_to_bv 64 15) by (rewrite (K24 16%bv) by ick; exact H16_23). assert (H17_24 : getr r24 17 = Z_to_bv 64 1024) by (rewrite (K24 17%bv) by ick; exact H17_23).
  assert (H5_24 : getr r24 5 = Z_to_bv 64 16) by (rewrite (K24 5%bv) by ick; exact H5_23). assert (H6_24 : getr r24 6 = Z_to_bv 64 17) by (rewrite (K24 6%bv) by ick; exact H6_23). assert (H7_24 : getr r24 7 = Z_to_bv 64 512) by (rewrite (K24 7%bv) by ick; exact H7_23).
  clear A23 B23 C23 H16_23 H17_23 H5_23 H6_23 H7_23 W23.
  destruct (art_ic_it_25 r24 M24 rom ca A24 B24 C24 H16_24 H17_24 H5_24 H6_24 H7_24 Hca Hca' W24) as (r25 & RUN25 & A25 & B25 & C25 & K25).
  match type of RUN25 with msteps _ _ (mkst _ _ ?X _) => set (M25 := X) in RUN25 end.
  assert (W25 : wrA M25 ca 2592) by (unfold M25; do 2 apply wr_Wn; exact W24).
  assert (H16_25 : getr r25 16 = Z_to_bv 64 15) by (rewrite (K25 16%bv) by ick; exact H16_24). assert (H17_25 : getr r25 17 = Z_to_bv 64 1024) by (rewrite (K25 17%bv) by ick; exact H17_24).
  assert (H5_25 : getr r25 5 = Z_to_bv 64 16) by (rewrite (K25 5%bv) by ick; exact H5_24). assert (H6_25 : getr r25 6 = Z_to_bv 64 17) by (rewrite (K25 6%bv) by ick; exact H6_24). assert (H7_25 : getr r25 7 = Z_to_bv 64 512) by (rewrite (K25 7%bv) by ick; exact H7_24).
  clear A24 B24 C24 H16_24 H17_24 H5_24 H6_24 H7_24 W24.
  destruct (art_ic_it_26 r25 M25 rom ca A25 B25 C25 H16_25 H17_25 H5_25 H6_25 H7_25 Hca Hca' W25) as (r26 & RUN26 & A26 & B26 & C26 & K26).
  match type of RUN26 with msteps _ _ (mkst _ _ ?X _) => set (M26 := X) in RUN26 end.
  assert (W26 : wrA M26 ca 2592) by (unfold M26; do 2 apply wr_Wn; exact W25).
  assert (H16_26 : getr r26 16 = Z_to_bv 64 15) by (rewrite (K26 16%bv) by ick; exact H16_25). assert (H17_26 : getr r26 17 = Z_to_bv 64 1024) by (rewrite (K26 17%bv) by ick; exact H17_25).
  assert (H5_26 : getr r26 5 = Z_to_bv 64 16) by (rewrite (K26 5%bv) by ick; exact H5_25). assert (H6_26 : getr r26 6 = Z_to_bv 64 17) by (rewrite (K26 6%bv) by ick; exact H6_25). assert (H7_26 : getr r26 7 = Z_to_bv 64 512) by (rewrite (K26 7%bv) by ick; exact H7_25).
  clear A25 B25 C25 H16_25 H17_25 H5_25 H6_25 H7_25 W25.
  destruct (art_ic_it_27 r26 M26 rom ca A26 B26 C26 H16_26 H17_26 H5_26 H6_26 H7_26 Hca Hca' W26) as (r27 & RUN27 & A27 & B27 & C27 & K27).
  match type of RUN27 with msteps _ _ (mkst _ _ ?X _) => set (M27 := X) in RUN27 end.
  assert (W27 : wrA M27 ca 2592) by (unfold M27; do 2 apply wr_Wn; exact W26).
  assert (H16_27 : getr r27 16 = Z_to_bv 64 15) by (rewrite (K27 16%bv) by ick; exact H16_26). assert (H17_27 : getr r27 17 = Z_to_bv 64 1024) by (rewrite (K27 17%bv) by ick; exact H17_26).
  assert (H5_27 : getr r27 5 = Z_to_bv 64 16) by (rewrite (K27 5%bv) by ick; exact H5_26). assert (H6_27 : getr r27 6 = Z_to_bv 64 17) by (rewrite (K27 6%bv) by ick; exact H6_26). assert (H7_27 : getr r27 7 = Z_to_bv 64 512) by (rewrite (K27 7%bv) by ick; exact H7_26).
  clear A26 B26 C26 H16_26 H17_26 H5_26 H6_26 H7_26 W26.
  destruct (art_ic_it_28 r27 M27 rom ca A27 B27 C27 H16_27 H17_27 H5_27 H6_27 H7_27 Hca Hca' W27) as (r28 & RUN28 & A28 & B28 & C28 & K28).
  match type of RUN28 with msteps _ _ (mkst _ _ ?X _) => set (M28 := X) in RUN28 end.
  assert (W28 : wrA M28 ca 2592) by (unfold M28; do 2 apply wr_Wn; exact W27).
  assert (H16_28 : getr r28 16 = Z_to_bv 64 15) by (rewrite (K28 16%bv) by ick; exact H16_27). assert (H17_28 : getr r28 17 = Z_to_bv 64 1024) by (rewrite (K28 17%bv) by ick; exact H17_27).
  assert (H5_28 : getr r28 5 = Z_to_bv 64 16) by (rewrite (K28 5%bv) by ick; exact H5_27). assert (H6_28 : getr r28 6 = Z_to_bv 64 17) by (rewrite (K28 6%bv) by ick; exact H6_27). assert (H7_28 : getr r28 7 = Z_to_bv 64 512) by (rewrite (K28 7%bv) by ick; exact H7_27).
  clear A27 B27 C27 H16_27 H17_27 H5_27 H6_27 H7_27 W27.
  destruct (art_ic_it_29 r28 M28 rom ca A28 B28 C28 H16_28 H17_28 H5_28 H6_28 H7_28 Hca Hca' W28) as (r29 & RUN29 & A29 & B29 & C29 & K29).
  match type of RUN29 with msteps _ _ (mkst _ _ ?X _) => set (M29 := X) in RUN29 end.
  assert (W29 : wrA M29 ca 2592) by (unfold M29; do 2 apply wr_Wn; exact W28).
  assert (H16_29 : getr r29 16 = Z_to_bv 64 15) by (rewrite (K29 16%bv) by ick; exact H16_28). assert (H17_29 : getr r29 17 = Z_to_bv 64 1024) by (rewrite (K29 17%bv) by ick; exact H17_28).
  assert (H5_29 : getr r29 5 = Z_to_bv 64 16) by (rewrite (K29 5%bv) by ick; exact H5_28). assert (H6_29 : getr r29 6 = Z_to_bv 64 17) by (rewrite (K29 6%bv) by ick; exact H6_28). assert (H7_29 : getr r29 7 = Z_to_bv 64 512) by (rewrite (K29 7%bv) by ick; exact H7_28).
  clear A28 B28 C28 H16_28 H17_28 H5_28 H6_28 H7_28 W28.
  destruct (art_ic_it_30 r29 M29 rom ca A29 B29 C29 H16_29 H17_29 H5_29 H6_29 H7_29 Hca Hca' W29) as (r30 & RUN30 & A30 & B30 & C30 & K30).
  match type of RUN30 with msteps _ _ (mkst _ _ ?X _) => set (M30 := X) in RUN30 end.
  assert (W30 : wrA M30 ca 2592) by (unfold M30; do 2 apply wr_Wn; exact W29).
  assert (H16_30 : getr r30 16 = Z_to_bv 64 15) by (rewrite (K30 16%bv) by ick; exact H16_29). assert (H17_30 : getr r30 17 = Z_to_bv 64 1024) by (rewrite (K30 17%bv) by ick; exact H17_29).
  assert (H5_30 : getr r30 5 = Z_to_bv 64 16) by (rewrite (K30 5%bv) by ick; exact H5_29). assert (H6_30 : getr r30 6 = Z_to_bv 64 17) by (rewrite (K30 6%bv) by ick; exact H6_29). assert (H7_30 : getr r30 7 = Z_to_bv 64 512) by (rewrite (K30 7%bv) by ick; exact H7_29).
  clear A29 B29 C29 H16_29 H17_29 H5_29 H6_29 H7_29 W29.
  destruct (art_ic_it_31 r30 M30 rom ca A30 B30 C30 H16_30 H17_30 H5_30 H6_30 H7_30 Hca Hca' W30) as (r31 & RUN31 & A31 & B31 & C31 & K31).
  match type of RUN31 with msteps _ _ (mkst _ _ ?X _) => set (M31 := X) in RUN31 end.
  assert (EM : M31 = art_ic_mem M ca 31). { unfold M31, M30, M29, M28, M27, M26, M25, M24, M23, M22, M21, M20, M19, M18, M17, M16, M15, M14, M13, M12, M11, M10, M9, M8, M7, M6, M5, M4, M3, M2, M1. cbn [art_ic_mem Z.of_nat Pos.of_succ_nat Pos.succ]. reflexivity. }
  rewrite EM in RUN31. exists r31. split.
  { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|]. eapply msteps_trans; [exact RUN9|]. eapply msteps_trans; [exact RUN10|]. eapply msteps_trans; [exact RUN11|]. eapply msteps_trans; [exact RUN12|]. eapply msteps_trans; [exact RUN13|]. eapply msteps_trans; [exact RUN14|]. eapply msteps_trans; [exact RUN15|]. eapply msteps_trans; [exact RUN16|]. eapply msteps_trans; [exact RUN17|]. eapply msteps_trans; [exact RUN18|]. eapply msteps_trans; [exact RUN19|]. eapply msteps_trans; [exact RUN20|]. eapply msteps_trans; [exact RUN21|]. eapply msteps_trans; [exact RUN22|]. eapply msteps_trans; [exact RUN23|]. eapply msteps_trans; [exact RUN24|]. eapply msteps_trans; [exact RUN25|]. eapply msteps_trans; [exact RUN26|]. eapply msteps_trans; [exact RUN27|]. eapply msteps_trans; [exact RUN28|]. eapply msteps_trans; [exact RUN29|]. eapply msteps_trans; [exact RUN30|]. exact RUN31. }
  intros r Hr. rewrite (K31 r Hr), (K30 r Hr), (K29 r Hr), (K28 r Hr), (K27 r Hr), (K26 r Hr), (K25 r Hr), (K24 r Hr), (K23 r Hr), (K22 r Hr), (K21 r Hr), (K20 r Hr), (K19 r Hr), (K18 r Hr), (K17 r Hr), (K16 r Hr), (K15 r Hr), (K14 r Hr), (K13 r Hr), (K12 r Hr), (K11 r Hr), (K10 r Hr), (K9 r Hr), (K8 r Hr), (K7 r Hr), (K6 r Hr), (K5 r Hr), (K4 r Hr), (K3 r Hr), (K2 r Hr), (K1 r Hr). reflexivity.
Qed.
End FPX.
