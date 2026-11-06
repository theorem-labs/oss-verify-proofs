(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1c5 X1by X1bo X1br X1c6.
Import ListNotations.

Definition core_feqv (c c' : core) : Prop :=
c_regs c = c_regs c' /\ regs_eqv (c_fregs c) (c_fregs c') /\
c_pc c = c_pc c' /\ c_fcsr c = c_fcsr c' /\ c_resv c = c_resv c'.

Inductive eff_feqv : eff -> eff -> Prop :=
| FEqvDone : forall c c', core_feqv c c' -> eff_feqv (EDone c) (EDone c')
| FEqvIllegal : forall c c', eff_feqv (EIllegal c) (EIllegal c')
| FEqvEcall : forall c c', eff_feqv (EEcall c) (EEcall c')
| FEqvEbreak : forall c c', eff_feqv (EEbreak c) (EEbreak c')
| FEqvFault : forall c c', eff_feqv (EFault c) (EFault c')
| FEqvDefinedIllegal : forall c c', eff_feqv (EDefinedIllegal c) (EDefinedIllegal c')
| FEqvLoad : forall n a k k', (forall v, eff_feqv (k v) (k' v)) -> eff_feqv (ELoad n a k) (ELoad n a k')
| FEqvStore : forall n a v k k', eff_feqv k k' -> eff_feqv (EStore n a v k) (EStore n a v k').

Lemma core_feqv_mk : forall R F F' pc fc rv, regs_eqv F F' ->
core_feqv (Core R F pc fc rv) (Core R F' pc fc rv).
Proof. intros. repeat split; assumption. Qed.

Local Ltac core_tac :=
unfold core_feqv, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv,
accrue, fwrite, inval_resv in *; simpl in *.

Lemma core_feqv_rset : forall r v c c', core_feqv c c' -> core_feqv (rset r v c) (rset r v c').
Proof.
intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (-> & HF & -> & -> & ->).
destruct (is_x0 r); simpl; repeat split; auto.
Qed.
Lemma core_feqv_fset : forall r v c c', core_feqv c c' -> core_feqv (fset r v c) (fset r v c').
Proof.
intros r v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (-> & HF & -> & -> & ->).
repeat split; auto using regs_eqv_set.
Qed.
Lemma core_feqv_with_pc : forall v c c', core_feqv c c' -> core_feqv (with_pc v c) (with_pc v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (-> & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_feqv_with_fcsr : forall v c c', core_feqv c c' -> core_feqv (with_fcsr v c) (with_fcsr v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (-> & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_feqv_with_resv : forall v c c', core_feqv c c' -> core_feqv (with_resv v c) (with_resv v c').
Proof. intros v [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (-> & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_feqv_accrue : forall fl c c', core_feqv c c' -> core_feqv (accrue fl c) (accrue fl c').
Proof. intros fl [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (-> & HF & -> & -> & ->). repeat split; auto. Qed.
Lemma core_feqv_fwrite : forall fmt r v c c', core_feqv c c' -> core_feqv (fwrite fmt r v c) (fwrite fmt r v c').
Proof. intros fmt r v c c' H. destruct fmt; apply core_feqv_fset; exact H. Qed.
Lemma core_feqv_inval_resv : forall a c c', core_feqv c c' -> core_feqv (inval_resv a c) (inval_resv a c').
Proof.
intros a [R F p f s] [R' F' p' f' s'] H. core_tac. destruct H as (-> & HF & -> & -> & ->).
destruct s' as [r|]; [destruct (Z.eqb _ _)|]; simpl; repeat split; auto.
Qed.
Lemma core_feqv_if : forall (b : bool) c1 c1' c2 c2',
core_feqv c1 c1' -> core_feqv c2 c2' -> core_feqv (if b then c1 else c2) (if b then c1' else c2').
Proof. intros [] c1 c1' c2 c2' H1 H2; assumption. Qed.

Local Ltac solve_core HF :=
repeat first [ apply core_feqv_rset | apply core_feqv_fset | apply core_feqv_with_pc
| apply core_feqv_with_fcsr | apply core_feqv_with_resv | apply core_feqv_accrue
| apply core_feqv_fwrite | apply core_feqv_inval_resv | apply core_feqv_if
| match goal with |- core_feqv (match ?X with _ => _ end) _ => destruct X end ];
apply (core_feqv_mk _ _ _ _ _ _ HF).

Local Ltac feqv_struct HF :=
repeat first
[ apply FEqvDone; solve_core HF
| apply FEqvIllegal | apply FEqvEcall | apply FEqvEbreak | apply FEqvFault | apply FEqvDefinedIllegal
| apply FEqvLoad; intros ?
| apply FEqvStore
| match goal with |- eff_feqv (match ?X with _ => _ end) _ => destruct X end
| match goal with |- eff_feqv (match ?X with _ => _ end _) _ => destruct X end ].

Local Ltac unfold_exec :=
cbv beta iota zeta delta [exec rget fget fread c_regs c_fregs c_pc c_fcsr c_resv
with_pc load_val store_val exec_csr resolve_rm frm_of].

Lemma exec_feqv_core : forall R F F' pc fc rv sz i,
regs_eqv F F' ->
eff_feqv (exec sz i (Core R F pc fc rv)) (exec sz i (Core R F' pc fc rv)).
Proof.
intros R F F' pc fc rv sz i HF.
destruct i; unfold_exec; rewrite ?HF; feqv_struct HF.
Qed.

Definition ms_feqv (ms ms' : machine_state) : Prop :=
ms_regs ms = ms_regs ms' /\ regs_eqv (ms_fregs ms) (ms_fregs ms') /\
ms_pc_val ms = ms_pc_val ms' /\ ms_svc_pending ms = ms_svc_pending ms' /\
ms_resv ms = ms_resv ms' /\ ms_fcsr ms = ms_fcsr ms' /\
ms_mem ms = ms_mem ms' /\ ms_rom ms = ms_rom ms'.

Lemma ms_feqv_refl : forall ms, ms_feqv ms ms.
Proof. intros ms. repeat split; try apply regs_eqv_refl. Qed.
Lemma ms_feqv_sym : forall ms ms', ms_feqv ms ms' -> ms_feqv ms' ms.
Proof. intros ms ms' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). repeat split; auto using regs_eqv_sym; congruence. Qed.
Lemma ms_feqv_trans : forall a b c, ms_feqv a b -> ms_feqv b c -> ms_feqv a c.
Proof.
intros a b c (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8) (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
repeat split; eauto using regs_eqv_trans; congruence.
Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma interp_eff_accesses_feqv : forall t t', eff_feqv t t' -> forall m,
match interp_eff_accesses segs t m, interp_eff_accesses segs t' m with
| MachineOk r, MachineOk r' =>
core_feqv (fst (access_value _ r)) (fst (access_value _ r')) /\
snd (access_value _ r) = snd (access_value _ r') /\
accessed_ranges _ r = accessed_ranges _ r'
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.
Proof.
intros t t' H. induction H; intros m; cbn [interp_eff_accesses access_value accessed_ranges fst snd]; auto.
- destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [| exact I].
specialize (H0 (bv_extract 0 n (le_bytes_to_word bs)) m).
destruct (interp_eff_accesses segs (k _) m) as [[[c1 m1] acc1]| |];
destruct (interp_eff_accesses segs (k' _) m) as [[[c1' m1'] acc1']| |];
cbn [access_value accessed_ranges fst snd] in *; try exact H0; try contradiction.
destruct H0 as (? & ? & ->). split; [assumption| split; [assumption| reflexivity]].
- destruct (store_ok segs m a (width_bytes n)); [| exact I].
specialize (IHeff_feqv (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))).
destruct (interp_eff_accesses segs k _) as [[[c1 m1] acc1]| |];
destruct (interp_eff_accesses segs k' _) as [[[c1' m1'] acc1']| |];
cbn [access_value accessed_ranges fst snd] in *; try exact IHeff_feqv; try contradiction.
destruct IHeff_feqv as (? & ? & ->). split; [assumption| split; [assumption| reflexivity]].
Qed.

Definition ares_feqv (r r' : machine_result (access_report machine_state)) : Prop :=
match r, r' with
| MachineOk a, MachineOk b =>
ms_feqv (access_value _ a) (access_value _ b) /\ accessed_ranges _ a = accessed_ranges _ b
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.
Definition res_feqv (r r' : machine_result machine_state) : Prop :=
match r, r' with
| MachineOk a, MachineOk b => ms_feqv a b
| MachineFault, MachineFault => True
| MachineUnmodeled, MachineUnmodeled => True
| _, _ => False
end.

#[using="Type"] Lemma decode_exec_accesses_feqv : forall ms ms' w, ms_feqv ms ms' ->
ares_feqv (decode_exec_accesses segs ms w) (decode_exec_accesses segs ms' w).
Proof.
intros ms ms' w Heqv.
destruct ms as [R F pc svc rv fc m ro], ms' as [R' F' pc' svc' rv' fc' m' ro'].
destruct Heqv as (HR & HF & Hpc & Hsvc & Hrv & Hfc & Hm & Hro); simpl in *; subst.
unfold decode_exec_accesses. destruct (is_ecall w).
- cbn [access_value accessed_ranges]. repeat split; assumption.
- destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); exact I].
cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom].
pose proof (interp_eff_accesses_feqv _ _ (exec_feqv_core R' F F' pc' fc' rv' (Z_to_bv 64 isz) i HF) m') as K.
destruct (interp_eff_accesses segs (exec _ i (Core R' F pc' fc' rv')) m') as [[[c m1] acc]| |];
destruct (interp_eff_accesses segs (exec _ i (Core R' F' pc' fc' rv')) m') as [[[c' m1'] acc']| |];
cbn [access_value accessed_ranges fst snd] in *; try exact K; try contradiction.
destruct K as ((H1 & H2 & H3 & H4 & H5) & -> & ->). repeat split; simpl; auto.
Qed.

#[using="Type"] Lemma step_accesses_feqv : forall ms ms', ms_feqv ms ms' ->
ares_feqv (step_accesses segs ms) (step_accesses segs ms').
Proof.
intros ms ms' Heqv. pose proof Heqv as (_ & _ & Hpc & _ & _ & _ & Hm & _).
unfold step_accesses, ms_pc. rewrite <- Hpc, <- Hm.
destruct (fetch_word segs (ms_pc_val ms)); [apply decode_exec_accesses_feqv; exact Heqv|].
destruct (fetch_word_ov segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_feqv; exact Heqv|].
destruct (fetch_tail_any segs (ms_mem ms) (ms_pc_val ms)); [apply decode_exec_accesses_feqv; exact Heqv|].
unfold fetch_failure. destruct (negb _); [exact I|]. destruct (_ || _)%bool; exact I.
Qed.

#[using="Type"] Lemma step_feqv : forall ms ms', ms_feqv ms ms' ->
res_feqv (RiscvSemantics.step segs ms) (RiscvSemantics.step segs ms').
Proof.
intros ms ms' Heqv. pose proof (step_accesses_feqv ms ms' Heqv) as K.
unfold RiscvSemantics.step.
destruct (step_accesses segs ms) as [a| |]; destruct (step_accesses segs ms') as [b| |];
cbn [drop_access_report] in *; try exact K. exact (proj1 K).
Qed.

#[using="Type"] Lemma mstep_feqv : forall a b a', ms_feqv a b -> mstep segs a a' ->
exists b', mstep segs b b' /\ ms_feqv a' b'.
Proof.
intros a b a' E [Hsvc Hst]. pose proof (step_feqv a b E) as K. rewrite Hst in K.
destruct (RiscvSemantics.step segs b) as [b'| |] eqn:Eb; cbn in K; try contradiction.
exists b'. split; [|exact K]. split; [|exact Eb].
destruct E as (_ & _ & _ & Hs & _). rewrite <- Hs. exact Hsvc.
Qed.

#[using="Type"] Lemma msteps_feqv : forall a a', msteps segs a a' -> forall b, ms_feqv a b ->
exists b', msteps segs b b' /\ ms_feqv a' b'.
Proof.
intros a a' H. induction H as [ms| ms ms1 ms2 Hs Hm IH]; intros b E.
- exists b. split; [apply msteps_refl| exact E].
- destruct (mstep_feqv ms b ms1 E Hs) as (b1 & Hb1 & E1).
destruct (IH b1 E1) as (b2 & Hb2 & E2).
exists b2. split; [eapply msteps_cons; eauto| exact E2].
Qed.

Definition feqv_closed (Q : machine_state -> Prop) : Prop :=
forall s t, ms_feqv s t -> Q s -> Q t.

#[using="Type"] Lemma evt_feqv : forall Q a b, ms_feqv a b -> feqv_closed Q -> evt segs Q a -> evt segs Q b.
Proof.
intros Q a b E CL (a' & Ha & HQ).
destruct (msteps_feqv a a' Ha b E) as (b' & Hb & E'). exists b'. split; [exact Hb|]. eapply CL; eauto.
Qed.

Definition fcanon (F : bvmap 5 word) : bvmap 5 word :=
mkF (reg_get F (Z_to_bv 5 0)) (reg_get F (Z_to_bv 5 1)) (reg_get F (Z_to_bv 5 2)) (reg_get F (Z_to_bv 5 3))
(reg_get F (Z_to_bv 5 4)) (reg_get F (Z_to_bv 5 5)) (reg_get F (Z_to_bv 5 6)) (reg_get F (Z_to_bv 5 7))
(reg_get F (Z_to_bv 5 8)) (reg_get F (Z_to_bv 5 9)) (reg_get F (Z_to_bv 5 10)) (reg_get F (Z_to_bv 5 11))
(reg_get F (Z_to_bv 5 12)) (reg_get F (Z_to_bv 5 13)) (reg_get F (Z_to_bv 5 14)) (reg_get F (Z_to_bv 5 15))
(reg_get F (Z_to_bv 5 16)) (reg_get F (Z_to_bv 5 17)) (reg_get F (Z_to_bv 5 18)) (reg_get F (Z_to_bv 5 19))
(reg_get F (Z_to_bv 5 20)) (reg_get F (Z_to_bv 5 21)) (reg_get F (Z_to_bv 5 22)) (reg_get F (Z_to_bv 5 23))
(reg_get F (Z_to_bv 5 24)) (reg_get F (Z_to_bv 5 25)) (reg_get F (Z_to_bv 5 26)) (reg_get F (Z_to_bv 5 27))
(reg_get F (Z_to_bv 5 28)) (reg_get F (Z_to_bv 5 29)) (reg_get F (Z_to_bv 5 30)) (reg_get F (Z_to_bv 5 31)).

#[using="Type"] Lemma fcanon_eqv : forall F, regs_eqv (fcanon F) F.
Proof.
intros F r. destruct (reg_of_nat r) as (n & -> & Hn).
do 32 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

#[using="Type"] Lemma ms_feqv_canon : forall R F pc fc sv m rom,
ms_feqv (MS R (fcanon F) pc fc sv m rom) (MS R F pc fc sv m rom).
Proof. intros. repeat split; try apply fcanon_eqv. Qed.

#[using="Type"] Lemma evt_canonF : forall Q R F pc fc sv m rom,
feqv_closed Q ->
evt segs Q (MS R (fcanon F) pc fc sv m rom) ->
evt segs Q (MS R F pc fc sv m rom).
Proof. intros Q R F pc fc sv m rom CL H. eapply evt_feqv; [apply ms_feqv_canon| exact CL| exact H]. Qed.

#[using="Type"] Lemma feqv_closed_exF : forall (P : bvmap 5 word -> machine_state -> Prop),
(forall F s t, ms_feqv s t -> P F s -> exists F', P F' t) ->
feqv_closed (fun ms => exists F, P F ms).
Proof. intros P H s t E [F HP]. eapply H; eauto. Qed.

#[using="Type"] Lemma ms_feqv_inv : forall R F pc fc sv m rom t,
ms_feqv (MS R F pc fc sv m rom) t -> exists F', regs_eqv F F' /\ t = MS R F' pc fc sv m rom.
Proof.
intros R F pc fc sv m rom [R' F' pc' sv' rv' fc' m' rom'] (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); simpl in *.
subst. exists F'. split; [exact H2| reflexivity].
Qed.
End WithSegs.
