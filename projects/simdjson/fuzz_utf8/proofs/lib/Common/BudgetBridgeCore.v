(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require TCodec.
Ltac2 tcn__Common_BudgetBridgeCore () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.LinuxProcessSem.Monad."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.BudgetBridgeCore."; "OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.BudgetBridgeCore.Sim."; "stdpp.bitvector.definitions."], [["1list"; "1nat"; "1prod"; "1unit"; "2eq"; "3Z"; "0L"; "0L1"; "0L2"; "4arg"; "4emit"; "4get_fds"; "4get_model"; "4get_vmmaps"; "4input"; "4modify"]; ["4sysno"; "5FdEntry"; "5Model"; "5SyscallInput"; "5VmMaps"; "5event"; "5m_vmmaps"; "5vm_limit"; "7Sim"; "6setlim"; "6setlimh"; "0e1"; "0e2"; "0f1"; "0f2"; "0k"]; ["0m"; "0m1"; "0m2"; "8bv"; "0x"]]).
Definition setlimh (L : Z) (h : VmMaps) : VmMaps :=
mkVmMapsFull (vm_reserved h) (vm_maps h) (vm_noaccess h) (vm_start_brk h)
(vm_brk h) L (vm_mmap_base h) (vm_init_sp h).
Definition setlimv (L : Z) (v : VmState) : VmState :=
mkVmState (setlimh L (vmst_maps v)) (vmst_lazy v) (vmst_materialized v).
Definition setlim (L : Z) (m : Model) : Model :=
mkModelOf (m_fd m) (setlimv L (m_vm m)) (m_io m) (m_fsys m) (m_proc m)
(m_lim m) (m_time m).
Lemma setlim_self : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeCore ";'B'4&I&G&Fr1%211%411%6213%83914pR2:1").
Proof.
intros [fd [[r ms na sb b l mb sp] lz mt] io fs pr lm tm]. reflexivity.
Qed.
Lemma setlim_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeCore ">'5'B'4&Ir3r2r1%4221%5241%6253%83921pR2:1pB<1p@=1").
Proof. reflexivity. Qed.
Lemma vm_limit_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeCore ">'5'B'4&G&F&Ir2r1%3221%511%711%93;15pR2;1p>=1").
Proof. reflexivity. Qed.
Lemma setlim_inj : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeCore "H'5'B'4&G&Fr2%211%411r1%511%711%93;41&Ir4r3%3221%423;%?3@21%@3A54p021p091pR6D1pR4E1p>G1").
Proof.
intros L m1 m2 Hl H.
rewrite <- (setlim_self m1), <- (setlim_self m2), Hl.
rewrite <- (setlim_setlim _ L m1), <- (setlim_setlim _ L m2), H. reflexivity.
Qed.
Section Sim.
Variable L : Z.
Definition liftO {A B} (F : B -> A) (o : outcome B) : outcome A :=
match o with
| Ok x m e => Ok (F x) (setlim L m) e
| Unmodeled => Unmodeled
end.
Definition Sim {A B} (F : B -> A) (c1 : Sys A) (c2 : Sys B) : Prop :=
forall i m,
(forall o1, c1 i (setlim L m) o1 -> exists o2, c2 i m o2 /\ o1 = liftO F o2)
/\ (forall o2, c2 i m o2 -> c1 i (setlim L m) (liftO F o2)).
Lemma sim_bind {A B C D} (F : B -> A) (G : D -> C) (c1 : Sys A) (c2 : Sys B)
(k1 : A -> Sys C) (k2 : B -> Sys D) :
Sim F c1 c2 -> (forall x, Sim G (k1 (F x)) (k2 x)) ->
Sim G (bind c1 k1) (bind c2 k2).
Proof.
intros Hc Hk i m. split.
- intros [y m2 evs|] H1; cbn in H1.
+ destruct H1 as (x & m1 & evs1 & evs2 & Hc1 & Hk1 & ->).
destruct (proj1 (Hc i m) _ Hc1) as ([x0 m0 e0|] & Hc2 & E); [|discriminate].
cbn in E. injection E as -> -> ->.
destruct (proj1 (Hk x0 i m0) _ Hk1) as ([y0 m3 e3|] & Hk2 & E'); [|discriminate].
cbn in E'. injection E' as -> -> ->.
exists (Ok y0 m3 (e0 ++ e3)). split; [|reflexivity].
exists x0, m0, e0, e3. auto.
+ exists Unmodeled. split; [|reflexivity].
destruct H1 as [Hc1 | (x & m1 & evs1 & Hc1 & Hk1)].
* destruct (proj1 (Hc i m) _ Hc1) as ([x0 m0 e0|] & Hc2 & E); [discriminate|].
left. exact Hc2.
* destruct (proj1 (Hc i m) _ Hc1) as ([x0 m0 e0|] & Hc2 & E); [|discriminate].
cbn in E. injection E as -> -> ->.
destruct (proj1 (Hk x0 i m0) _ Hk1) as ([y0 m3 e3|] & Hk2 & E'); [discriminate|].
right. exists x0, m0, e0. auto.
- intros [y m2 evs|] H2; cbn in H2 |- *.
+ destruct H2 as (x & m1 & evs1 & evs2 & Hc2 & Hk2 & ->).
pose proof (proj2 (Hc i m) _ Hc2) as Hc1. cbn in Hc1.
pose proof (proj2 (Hk x i m1) _ Hk2) as Hk1. cbn in Hk1.
exists (F x), (setlim L m1), evs1, evs2. auto.
+ destruct H2 as [Hc2 | (x & m1 & evs1 & Hc2 & Hk2)].
* left. exact (proj2 (Hc i m) _ Hc2).
* right. pose proof (proj2 (Hc i m) _ Hc2) as Hc1. cbn in Hc1.
pose proof (proj2 (Hk x i m1) _ Hk2) as Hk1. cbn in Hk1.
exists (F x), (setlim L m1), evs1. auto.
Qed.
Lemma sim_pure {A B} (F : B -> A) (x1 : A) (x2 : B) :
x1 = F x2 -> Sim F (pure x1) (pure x2).
Proof.
intros -> i m. unfold pure. split.
- intros o1 ->. exists (Ok x2 m []). split; reflexivity.
- intros o2 ->. reflexivity.
Qed.
Lemma sim_get : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeCore "7&H'B&Iv6%211&<%6555211").
Proof.
intros i m. unfold get_model. split.
- intros o1 ->. exists (Ok m m []). split; reflexivity.
- intros o2 ->. reflexivity.
Qed.
Lemma sim_modify : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeCore "H'Bp011'4r3&Iv6r1%3221%511r2%114%7261%:3<41pR2=1&H'3qR:1:&?%11?%21:%6555421p081pQNE1pQLF1").
Proof. intros f1 f2.
intros Hf i m. unfold modify. split.
- intros o1 ->. exists (Ok tt (f2 m) []). split; [reflexivity|]. cbn. rewrite Hf. reflexivity.
- intros o2 ->. cbn. rewrite Hf. reflexivity.
Qed.
Lemma sim_choose {A} (P1 P2 : A -> Prop) :
(forall x, P1 x <-> P2 x) -> Sim (fun x : A => x) (choose P1) (choose P2).
Proof.
intros HP i m. unfold choose. split.
- intros o1 (x & Hx & ->). exists (Ok x m []). split; [|reflexivity].
exists x. split; [apply HP; exact Hx | reflexivity].
- intros o2 (x & Hx & ->). exists x. split; [apply HP; exact Hx | reflexivity].
Qed.
Lemma sim_choose_gen {A B} (F : B -> A) (P1 : A -> Prop) (P2 : B -> Prop) :
(forall x1, P1 x1 -> exists x2, P2 x2 /\ x1 = F x2) ->
(forall x2, P2 x2 -> P1 (F x2)) ->
Sim F (choose P1) (choose P2).
Proof.
intros H12 H21 i m. unfold choose. split.
- intros o1 (x & Hx & ->). destruct (H12 x Hx) as (x2 & Hx2 & ->).
exists (Ok x2 m []). split; [|reflexivity]. exists x2. auto.
- intros o2 (x & Hx & ->). exists (F x). split; [apply H21; exact Hx | reflexivity].
Qed.
Lemma sim_alt {A B} (F : B -> A) (c1 d1 : Sys A) (c2 d2 : Sys B) :
Sim F c1 c2 -> Sim F d1 d2 -> Sim F (alt c1 d1) (alt c2 d2).
Proof.
intros Hc Hd i m. unfold alt. split.
- intros o1 [H | H].
+ destruct (proj1 (Hc i m) _ H) as (o2 & H2 & E). exists o2. auto.
+ destruct (proj1 (Hd i m) _ H) as (o2 & H2 & E). exists o2. auto.
- intros o2 [H | H].
+ left. exact (proj2 (Hc i m) _ H).
+ right. exact (proj2 (Hd i m) _ H).
Qed.
Lemma sim_unmodeled {A B} (F : B -> A) : Sim F unmodeled unmodeled.
Proof.
intros i m. unfold unmodeled. split.
- intros o1 ->. exists Unmodeled. split; reflexivity.
- intros o2 ->. reflexivity.
Qed.
Lemma sim_emit : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeCore "B'0'E%211'4r2r1%33421&H'3qR:14&:r3%211%319%7566521p091pQJ>1pQH?1").
Proof. intros e1 e2.
intros <- i m. unfold emit. split.
- intros o1 ->. exists (Ok tt m e1). split; reflexivity.
- intros o2 ->. reflexivity.
Qed.
Lemma sim_input : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeCore "6&H'Cr1qR:21&>%5544211").
Proof.
intros i m. unfold input. split.
- intros o1 ->. exists (Ok i m []). split; reflexivity.
- intros o2 ->. reflexivity.
Qed.
Lemma sim_sysno : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeCore "8&H'Q3yR0%211r1qR:21&@%7544211").
Proof.
intros i m. unfold sysno. split.
- intros o1 ->. exists (Ok (in_sysno i) m []). split; reflexivity.
- intros o2 ->. reflexivity.
Qed.
Lemma sim_arg : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeCore ";'1&H'Q3yR0%211r1qR:21&9%113%8555311pR0:1").
Proof. intros k.
intros i m. unfold arg. split.
- intros o1 ->. exists (Ok (in_arg i k) m []). split; reflexivity.
- intros o2 ->. reflexivity.
Qed.
Lemma sim_get_fds : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeCore "=&H'0'2'Q3yR0%211'A%5221%711r1qR:21&;%<544211").
Proof.
intros i m. unfold get_fds. split.
- intros o1 ->. exists (Ok (m_fds m) m []). split; reflexivity.
- intros o2 ->. reflexivity.
Qed.
Lemma sim_get_vmmaps : ltac2:(TCodec.tc2 tcn__Common_BudgetBridgeCore "7&H'D&Jv6%211&=%6555211").
Proof.
intros i m. unfold get_vmmaps. split.
- intros o1 ->. exists (Ok (m_vmmaps m) m []). split; reflexivity.
- intros o2 ->. reflexivity.
Qed.
Lemma sim_reader {A B} (F : B -> A) (s1 : SyscallInput -> Sys A) (s2 : SyscallInput -> Sys B) :
(forall j, Sim F (s1 j) (s2 j)) ->
Sim F (fun i => s1 i i) (fun i => s2 i i).
Proof. intros H i m. exact (H i i m). Qed.
Lemma sim_ext {A B} (F : B -> A) (c1 c1' : Sys A) (c2 c2' : Sys B) :
(forall i m o, c1 i m o <-> c1' i m o) ->
(forall i m o, c2 i m o <-> c2' i m o) ->
Sim F c1' c2' -> Sim F c1 c2.
Proof.
intros E1 E2 H i m. split.
- intros o1 H1. apply E1 in H1. destruct (proj1 (H i m) _ H1) as (o2 & H2 & E).
exists o2. split; [apply E2; exact H2 | exact E].
- intros o2 H2. apply E2 in H2. apply E1. exact (proj2 (H i m) _ H2).
Qed.
Lemma sim_nat {A} (c : Sys A) :
Sim (fun x => x) c c ->
forall i m o, c i (setlim L m) o <-> exists o0, c i m o0 /\ o = liftO (fun x => x) o0.
Proof.
intros H i m o. split.
- apply (proj1 (H i m)).
- intros (o0 & H0 & ->). exact (proj2 (H i m) _ H0).
Qed.
Definition Sim1 {A B} (F : B -> A) (c1 : Sys A) (c2 : Sys B)
(i : SyscallInput) (m : Model) : Prop :=
(forall o1, c1 i (setlim L m) o1 -> exists o2, c2 i m o2 /\ o1 = liftO F o2)
/\ (forall o2, c2 i m o2 -> c1 i (setlim L m) (liftO F o2)).
Lemma sim1_of_sim {A B} (F : B -> A) c1 c2 :
Sim F c1 c2 -> forall i m, Sim1 F c1 c2 i m.
Proof. intros H i m. exact (H i m). Qed.
Lemma sim1_bind {A B C D} (F : B -> A) (G : D -> C) (c1 : Sys A) (c2 : Sys B)
(k1 : A -> Sys C) (k2 : B -> Sys D) i m :
Sim1 F c1 c2 i m ->
(forall x m' e, c2 i m (Ok x m' e) -> Sim1 G (k1 (F x)) (k2 x) i m') ->
Sim1 G (bind c1 k1) (bind c2 k2) i m.
Proof.
intros Hc Hk. split.
- intros [y m2 evs|] H1; cbn in H1.
+ destruct H1 as (x & m1 & evs1 & evs2 & Hc1 & Hk1 & ->).
destruct (proj1 Hc _ Hc1) as ([x0 m0 e0|] & Hc2 & E); [|discriminate].
cbn in E. injection E as -> -> ->.
destruct (proj1 (Hk x0 m0 e0 Hc2) _ Hk1) as ([y0 m3 e3|] & Hk2 & E'); [|discriminate].
cbn in E'. injection E' as -> -> ->.
exists (Ok y0 m3 (e0 ++ e3)). split; [|reflexivity].
exists x0, m0, e0, e3. auto.
+ exists Unmodeled. split; [|reflexivity].
destruct H1 as [Hc1 | (x & m1 & evs1 & Hc1 & Hk1)].
* destruct (proj1 Hc _ Hc1) as ([x0 m0 e0|] & Hc2 & E); [discriminate|].
left. exact Hc2.
* destruct (proj1 Hc _ Hc1) as ([x0 m0 e0|] & Hc2 & E); [|discriminate].
cbn in E. injection E as -> -> ->.
destruct (proj1 (Hk x0 m0 e0 Hc2) _ Hk1) as ([y0 m3 e3|] & Hk2 & E'); [discriminate|].
right. exists x0, m0, e0. auto.
- intros [y m2 evs|] H2; cbn in H2 |- *.
+ destruct H2 as (x & m1 & evs1 & evs2 & Hc2 & Hk2 & ->).
pose proof (proj2 Hc _ Hc2) as Hc1. cbn in Hc1.
pose proof (proj2 (Hk x m1 evs1 Hc2) _ Hk2) as Hk1. cbn in Hk1.
exists (F x), (setlim L m1), evs1, evs2. auto.
+ destruct H2 as [Hc2 | (x & m1 & evs1 & Hc2 & Hk2)].
* left. exact (proj2 Hc _ Hc2).
* right. pose proof (proj2 Hc _ Hc2) as Hc1. cbn in Hc1.
pose proof (proj2 (Hk x m1 evs1 Hc2) _ Hk2) as Hk1. cbn in Hk1.
exists (F x), (setlim L m1), evs1. auto.
Qed.
Lemma sim1_choose {A} (P1 P2 : A -> Prop) i m :
(forall x, P1 x <-> P2 x) -> Sim1 (fun x : A => x) (choose P1) (choose P2) i m.
Proof. intros HP. exact (sim_choose P1 P2 HP i m). Qed.
Lemma sim1_alt {A B} (F : B -> A) (c1 d1 : Sys A) (c2 d2 : Sys B) i m :
Sim1 F c1 c2 i m -> Sim1 F d1 d2 i m -> Sim1 F (alt c1 d1) (alt c2 d2) i m.
Proof.
intros Hc Hd. unfold alt. split.
- intros o1 [H | H].
+ destruct (proj1 Hc _ H) as (o2 & H2 & E). exists o2. auto.
+ destruct (proj1 Hd _ H) as (o2 & H2 & E). exists o2. auto.
- intros o2 [H | H].
+ left. exact (proj2 Hc _ H).
+ right. exact (proj2 Hd _ H).
Qed.
Lemma sim1_nat {A} (c : Sys A) i m :
Sim1 (fun x => x) c c i m ->
forall o, c i (setlim L m) o <-> exists o0, c i m o0 /\ o = liftO (fun x => x) o0.
Proof.
intros H o. split.
- apply (proj1 H).
- intros (o0 & H0 & ->). exact (proj2 H _ H0).
Qed.
End Sim.
