(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QWxq_c1 Qe4Y Qod2 QdTb Q1lV QHWH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QsjA QEpW QWxq_c1.
Import Qe4Y Qod2.

Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope bv_scope.

Lemma tset_same_id {X} : forall (p : positive) (x : X) t, tget p t = Some x -> tset p x t = t.
Proof.
induction p as [p IH|p IH|]; intros x [|l v r] H; simpl in *; try discriminate.
- rewrite (IH x r H). reflexivity.
- rewrite (IH x l H). reflexivity.
- subst v. reflexivity.
Qed.

Lemma bvmap_set_same_id : forall (k : reg) (v : word) (R : bvmap 5 word), bvmap_get k R = Some v -> bvmap_set k v R = R.
Proof. intros k v R H. unfold bvmap_set, bvmap_get in *. apply tset_same_id. exact H. Qed.

Definition keys5 : list reg := map (fun n => Z_to_bv 5 (Z.of_nat n)) (seq 0 32).
Definition is_absent (R : bvmap 5 word) (k : reg) : bool := match bvmap_get k R with None => true | Some _ => false end.
Definition absent (R : bvmap 5 word) : nat := length (List.filter (is_absent R) keys5).

Lemma keys5_all : forall r : reg, In r keys5.
Proof.
intros r. destruct (reg_of_nat' r) as (n & -> & Hn). unfold keys5. apply in_map_iff. exists n. split; [reflexivity|].
apply in_seq. lia.
Qed.

Lemma filter_length_lt {X} : forall (p q : X -> bool) l x, In x l -> p x = true -> q x = false ->
(forall y, q y = true -> p y = true) -> (length (List.filter q l) < length (List.filter p l))%nat.
Proof.
intros p q l x Hin Hp Hq Himp.
assert (LE : forall l', (length (List.filter q l') <= length (List.filter p l'))%nat).
{ induction l' as [|a l' IH]; [simpl; lia|]. simpl. destruct (q a) eqn:Eq.
- rewrite (Himp a Eq). simpl. lia.
- destruct (p a); simpl; lia. }
induction l as [|a l IH]; [destruct Hin|]. destruct Hin as [E|Hin].
- subst a. simpl. rewrite Hp, Hq. simpl. pose proof (LE l). lia.
- specialize (IH Hin). simpl. destruct (q a) eqn:Eq.
+ rewrite (Himp a Eq). simpl. lia.
+ destruct (p a); simpl; lia.
Qed.

Lemma absent_set_lt : forall (k : reg) v R, bvmap_get k R = None -> (absent (bvmap_set k v R) < absent R)%nat.
Proof.
intros k v R H. unfold absent. apply (filter_length_lt (is_absent R) (is_absent (bvmap_set k v R)) keys5 k (keys5_all k)).
- unfold is_absent. rewrite H. reflexivity.
- unfold is_absent. rewrite bvmap_get_set_same. reflexivity.
- intros y Hy. unfold is_absent in *. destruct (bv_eqb k y) eqn:E.
+ apply bv_eqb_eq in E. subst y. rewrite bvmap_get_set_same in Hy. discriminate.
+ rewrite bvmap_get_set_other in Hy; [exact Hy|]. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Definition tshape (R0 R : bvmap 5 word) : Prop := R = R0 \/ exists (k : reg) (v : word), is_x0 k = false /\ R = bvmap_set k v R0.
Definition fshape (F0 F : bvmap 5 word) : Prop := F = F0 \/ exists (k : reg) (v : word), F = bvmap_set k v F0.

Section Shape.
Variables R0 F0 : bvmap 5 word.

Definition sh (a b : bool) (c : core) : Prop :=
(if a then tshape R0 (c_regs c) else c_regs c = R0) /\ (if b then fshape F0 (c_fregs c) else c_fregs c = F0).

Lemma sh_base : forall a b pc fc rv, sh a b (Core R0 F0 pc fc rv).
Proof. intros [|] [|] pc fc rv; split; simpl; try reflexivity; left; reflexivity. Qed.

Local Ltac core_tac :=
unfold sh, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv, accrue, fwrite, inval_resv in *; simpl in *.

Lemma sh_rset : forall b r v c, sh false b c -> sh true b (rset r v c).
Proof.
intros b r v [R F p f s] [H1 H2]. core_tac. subst R. destruct (is_x0 r) eqn:E; simpl; (split; [|exact H2]).
- left. reflexivity.
- right. exists r, v. split; [exact E| reflexivity].
Qed.
Lemma sh_fset : forall a r v c, sh a false c -> sh a true (fset r v c).
Proof. intros a r v [R F p f s] [H1 H2]. core_tac. subst F. split; [exact H1|]. right. exists r, v. reflexivity. Qed.
Lemma sh_fwrite : forall a fmt r v c, sh a false c -> sh a true (fwrite fmt r v c).
Proof. intros a fmt r v c H. destruct fmt; apply sh_fset; exact H. Qed.
Lemma sh_with_pc : forall a b v c, sh a b c -> sh a b (with_pc v c).
Proof. intros a b v [R F p f s] H. core_tac. exact H. Qed.
Lemma sh_with_fcsr : forall a b v c, sh a b c -> sh a b (with_fcsr v c).
Proof. intros a b v [R F p f s] H. core_tac. exact H. Qed.
Lemma sh_with_resv : forall a b v c, sh a b c -> sh a b (with_resv v c).
Proof. intros a b v [R F p f s] H. core_tac. exact H. Qed.
Lemma sh_accrue : forall a b fl c, sh a b c -> sh a b (accrue fl c).
Proof. intros a b fl [R F p f s] H. core_tac. exact H. Qed.
Lemma sh_inval_resv : forall a b x c, sh a b c -> sh a b (inval_resv x c).
Proof. intros a b x [R F p f s] H. core_tac. destruct s as [r|]; [destruct (Z.eqb _ _)|]; simpl; exact H. Qed.
Lemma sh_if : forall a b (t : bool) c1 c2, sh a b c1 -> sh a b c2 -> sh a b (if t then c1 else c2).
Proof. intros a b [] c1 c2 H1 H2; assumption. Qed.

Lemma sh_weak_r : forall b c, sh false b c -> sh true b c.
Proof. intros b c [H1 H2]. split; [left; exact H1| exact H2]. Qed.
Lemma sh_weak_f : forall a c, sh a false c -> sh a true c.
Proof. intros a c [H1 H2]. split; [exact H1| left; exact H2]. Qed.

Inductive eff_sh : eff -> Prop :=
| ShDone : forall c, sh true true c -> eff_sh (EDone c)
| ShIllegal : forall c, eff_sh (EIllegal c)
| ShEcall : forall c, eff_sh (EEcall c)
| ShEbreak : forall c, eff_sh (EEbreak c)
| ShFault : forall c, eff_sh (EFault c)
| ShDefIllegal : forall c, eff_sh (EDefinedIllegal c)
| ShLoad : forall n a k, (forall v, eff_sh (k v)) -> eff_sh (ELoad n a k)
| ShStore : forall n a v k, eff_sh k -> eff_sh (EStore n a v k).

Local Ltac solve_sh :=
repeat first [ apply sh_rset | apply sh_fset | apply sh_fwrite | apply sh_with_pc
| apply sh_with_fcsr | apply sh_with_resv | apply sh_accrue | apply sh_inval_resv | apply sh_if
| match goal with |- sh _ _ (match ?X with _ => _ end) => destruct X end ];
apply sh_base.

Local Ltac sh_struct :=
repeat first
[ apply ShDone; solve_sh
| apply ShIllegal | apply ShEcall | apply ShEbreak | apply ShFault | apply ShDefIllegal
| apply ShLoad; intros ?
| apply ShStore
| match goal with |- eff_sh (match ?X with _ => _ end) => destruct X end
| match goal with |- eff_sh (match ?X with _ => _ end _) => destruct X end ].

Local Ltac unfold_exec :=
cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
with_pc load_val store_val exec_csr resolve_rm frm_of].

Lemma exec_sh : forall pc fc rv sz i, eff_sh (exec sz i (Core R0 F0 pc fc rv)).
Proof.
intros pc fc rv sz i.
destruct i; unfold_exec; sh_struct.
Qed.
End Shape.

Section Step.
Variable segs : list Segment.

Lemma interp_sh : forall R0 F0 t, eff_sh R0 F0 t -> forall m r,
interp_eff_accesses segs t m = MachineOk r -> sh R0 F0 true true (fst (@access_value _ r)).
Proof.
intros R0 F0 t H. induction H as [c Hc|c|c|c|c|c|n a k Hk IH|n a v k Hk IH]; intros m r E; cbn [interp_eff_accesses] in E; try discriminate.
- injection E as <-. cbn. exact Hc.
- destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r'| |] eqn:E'; try discriminate.
injection E as <-. cbn. exact (IH _ m r' E').
- destruct (store_ok segs m a (width_bytes n)); [|discriminate].
destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [r'| |] eqn:E'; try discriminate.
injection E as <-. cbn. exact (IH _ r' E').
Qed.

Lemma decode_exec_sh : forall ms w r, decode_exec_accesses segs ms w = MachineOk r ->
tshape (ms_regs ms) (ms_regs (@access_value _ r)) /\ fshape (ms_fregs ms) (ms_fregs (@access_value _ r)).
Proof.
intros ms w r E. unfold decode_exec_accesses in E. destruct (is_ecall w).
{ injection E as <-. cbn. split; left; reflexivity. }
destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
match type of E with context [interp_eff_accesses segs ?t ?m] =>
destruct (interp_eff_accesses segs t m) as [rep| |] eqn:EI; try discriminate;
pose proof (interp_sh _ _ t (exec_sh (ms_regs ms) (ms_fregs ms) _ _ _ _ i) m rep EI) as [S1 S2] end.
destruct (@access_value _ rep) as [c m'] eqn:EV. injection E as <-. cbn in *. split; assumption.
Qed.

Lemma step_shape : forall ms ms', RiscvSemantics.step segs ms = MachineOk ms' ->
tshape (ms_regs ms) (ms_regs ms') /\ fshape (ms_fregs ms) (ms_fregs ms').
Proof.
intros ms ms' E. unfold RiscvSemantics.step, drop_access_report in E.
destruct (step_accesses segs ms) as [r| |] eqn:ES; try discriminate. injection E as <-.
unfold step_accesses in ES.
repeat match type of ES with
| context [match ?X with Some _ => _ | None => _ end] => destruct X
end; try (apply (decode_exec_sh _ _ _ ES)).
unfold fetch_failure in ES.
repeat match type of ES with context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

Lemma is_x0_eqb : forall k : reg, is_x0 k = false -> bv_eqb k 0 = false.
Proof. intros k H. unfold is_x0 in H. unfold bv_eqb. exact H. Qed.

Lemma tshape_fix : forall R0 R Rc, tshape R0 R -> iregs_eqv Rc R0 -> iregs_eqv Rc R -> R = R0 \/ (absent R < absent R0)%nat.
Proof.
intros R0 R Rc [->|(k & v & Hk & ->)] E0 E1; [left; reflexivity|].
destruct (bvmap_get k R0) as [v'|] eqn:G; [left | right; apply absent_set_lt; exact G].
apply bvmap_set_same_id. rewrite G. f_equal.
pose proof (iregs_eqv_nz _ _ k E0 (is_x0_eqb k Hk)) as A0. pose proof (iregs_eqv_nz _ _ k E1 (is_x0_eqb k Hk)) as A1.
rewrite reg_get_set_same in A1. unfold reg_get in A0 at 2. rewrite G in A0. congruence.
Qed.
Lemma fshape_fix : forall F0 F Fc, fshape F0 F -> regs_eqv Fc F0 -> regs_eqv Fc F -> F = F0 \/ (absent F < absent F0)%nat.
Proof.
intros F0 F Fc [->|(k & v & ->)] E0 E1; [left; reflexivity|].
destruct (bvmap_get k F0) as [v'|] eqn:G; [left | right; apply absent_set_lt; exact G].
apply bvmap_set_same_id. rewrite G. f_equal.
pose proof (E0 k) as A0. pose proof (E1 k) as A1.
rewrite reg_get_set_same in A1. unfold reg_get in A0 at 2. rewrite G in A0. congruence.
Qed.

Lemma ms_eq_intro : forall a b : machine_state, ms_regs a = ms_regs b -> ms_fregs a = ms_fregs b -> ms_pc_val a = ms_pc_val b ->
ms_svc_pending a = ms_svc_pending b -> ms_resv a = ms_resv b -> ms_fcsr a = ms_fcsr b -> ms_mem a = ms_mem b -> ms_rom a = ms_rom b -> a = b.
Proof. intros [] []; simpl; intros; subst; reflexivity. Qed.

Lemma spin_fix : forall n msc mo mss,
(absent (ms_regs mss) + absent (ms_fregs mss) <= n)%nat -> ms_eqv msc mss -> ms_svc_pending msc = None ->
mi_account_step segs msc mo = MachineOk (msc, mo) -> QHWH.to_spin segs mss mo.
Proof.
induction n as [|n IH]; intros msc mo mss Hn Heqv Hsvc Hfix;
(pose proof (mi_account_step_eqv segs msc mss mo Heqv) as K; rewrite Hfix in K;
destruct (mi_account_step segs mss mo) as [[ms1 mo1]| |] eqn:E1; cbn in K; try contradiction; destruct K as [K1 <-];
pose proof (mi_account_step_projects segs mss mo ms1 mo E1) as ST; destruct (step_shape mss ms1 ST) as [SR SF];
pose proof Heqv as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); pose proof K1 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8);
assert (Hsvc' : ms_svc_pending mss = None) by congruence;
destruct (tshape_fix _ _ _ SR H1 G1) as [ER|LR]; destruct (fshape_fix _ _ _ SF H2 G2) as [EF|LF];
try (assert (ms1 = mss) as -> by (apply ms_eq_intro; congruence); exact (QHWH.ts_spin segs mss mo Hsvc' E1))).
all: try (exfalso; rewrite ?ER, ?EF in *; lia).
all: apply (QHWH.ts_step segs mss mo ms1 mo Hsvc' E1); apply (IH msc mo ms1); [rewrite ?ER, ?EF in *; lia | exact K1 | exact Hsvc | exact Hfix].
Qed.

Theorem to_spin_eqv : forall ms mo, QHWH.to_spin segs ms mo -> forall ms', ms_eqv ms ms' -> QHWH.to_spin segs ms' mo.
Proof.
intros ms mo H. induction H as [ms mo Hsvc Hfix | ms mo ms1 mo1 Hsvc Hst _ IH]; intros ms' Heqv.
- exact (spin_fix _ ms mo ms' (le_n _) Heqv Hsvc Hfix).
- pose proof (mi_account_step_eqv segs ms ms' mo Heqv) as K. rewrite Hst in K.
destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E1; cbn in K; try contradiction. destruct K as [K1 <-].
destruct Heqv as (_ & _ & _ & H4 & _).
exact (QHWH.ts_step segs ms' mo ms1' mo1 ltac:(congruence) E1 (IH ms1' K1)).
Qed.

Notation cfg_eqv := (Qe4Y.cfg_eqv).

Theorem srealizes_eqv_mut :
(forall c T, Q1lV.srealizes segs c T -> forall c', cfg_eqv c c' -> Q1lV.srealizes segs c' T)
/\ (forall V T c, Q1lV.slbody segs V T c -> forall c', cfg_eqv c c' -> Q1lV.slbody segs (eclo V) T c').
Proof.
apply (Q1lV.srealizes_slbody_mutind segs
(fun c T _ => forall c', cfg_eqv c c' -> Q1lV.srealizes segs c' T)
(fun V T c _ => forall c', cfg_eqv c c' -> Q1lV.slbody segs (eclo V) T c')).
-  intros c I evs nx T i0 Hnode Hcont IH c' Heqv.
destruct (node_ok_tr segs c c' I evs nx Heqv Hnode) as [Hnode' Hnx].
apply (Q1lV.srz_node segs c' I evs (fun i => nx_tr segs c' (nx i)) T i0 Hnode'). intros i. apply (IH i). apply Hnx.
-  intros c Hh [ms' md'] [_ Hmd]. apply Q1lV.srz_halt. cbn in Hmd |- *. rewrite <- Hmd. exact Hh.
-  intros [ms md] Hs Hh [ms' md'] [Hms Hmd]. cbn in Hmd, Hs, Hh, Hms. subst md'.
apply Q1lV.srz_spin; cbn; [exact (to_spin_eqv ms md Hs ms' Hms)| exact Hh].
-  intros c T T' H IH Heq c' Heqv. eapply Q1lV.srz_conseq; [apply IH; exact Heqv| exact Heq].
-  intros V T c c_e HV Hbody IHbody Hstar He IHe c' Heqv.
destruct (star_eqv segs c [] c_e Hstar c' Heqv) as (c_e' & Hstar' & He').
apply (Q1lV.srz_loop segs (eclo V) T c' c_e').
+ exists c. split; [exact HV| exact Heqv].
+ intros c1 (c0 & HV0 & H01). exact (IHbody c0 HV0 c1 H01).
+ exact Hstar'.
+ apply IHe. exact He'.
-  intros V T c H IH c' Heqv. apply Q1lV.slb_exit. apply IH. exact Heqv.
-  intros V T c I nx k Hnode Hk IHk Hv c' Heqv.
destruct (node_ok_tr segs c c' I (fun _ => []) nx Heqv Hnode) as [Hnode' Hnx].
apply (Q1lV.slb_node segs (eclo V) T c' I (fun i => nx_tr segs c' (nx i)) k Hnode').
+ intros i Hi. apply (IHk i Hi). apply Hnx.
+ intros i Hi. exists (nx i). split; [exact (Hv i Hi)| apply Hnx].
Qed.

Theorem srealizes_eqv : forall c c' T, cfg_eqv c c' -> Q1lV.srealizes segs c T -> Q1lV.srealizes segs c' T.
Proof. intros c c' T Heqv H. exact (proj1 srealizes_eqv_mut c T H c' Heqv). Qed.

Theorem srealizes_canon : forall R F pc fc rv m ro md T,
Q1lV.srealizes segs (mkCfg (MS (canonR R) F pc fc rv m ro) md) T ->
Q1lV.srealizes segs (mkCfg (MS R F pc fc rv m ro) md) T.
Proof.
intros R F pc fc rv m ro md T H. eapply srealizes_eqv; [| exact H].
split; [| reflexivity]. apply ms_eqv_sym. apply ms_eqv_canon.
Qed.
End Step.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsjA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe4Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qe4Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qod2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qod2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdTb. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1lV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHWH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope bv_scope.

Lemma tset_same_id {X} : forall (p : positive) (x : X) t, tget p t = Some x -> tset p x t = t.
Proof.
induction p as [p IH|p IH|]; intros x [|l v r] H; simpl in *; try discriminate.
- rewrite (IH x r H). reflexivity.
- rewrite (IH x l H). reflexivity.
- subst v. reflexivity.
Qed.

Lemma bvmap_set_same_id : forall (k : reg) (v : word) (R : bvmap 5 word), bvmap_get k R = Some v -> bvmap_set k v R = R.
Proof. intros k v R H. unfold bvmap_set, bvmap_get in *. apply tset_same_id. exact H. Qed.

Definition keys5 : list reg := map (fun n => Z_to_bv 5 (Z.of_nat n)) (seq 0 32).
Definition is_absent (R : bvmap 5 word) (k : reg) : bool := match bvmap_get k R with None => true | Some _ => false end.
Definition absent (R : bvmap 5 word) : nat := length (List.filter (is_absent R) keys5).

Lemma keys5_all : forall r : reg, In r keys5.
Proof.
intros r. destruct (reg_of_nat' r) as (n & -> & Hn). unfold keys5. apply in_map_iff. exists n. split; [reflexivity|].
apply in_seq. lia.
Qed.

Lemma filter_length_lt {X} : forall (p q : X -> bool) l x, In x l -> p x = true -> q x = false ->
(forall y, q y = true -> p y = true) -> (length (List.filter q l) < length (List.filter p l))%nat.
Proof.
intros p q l x Hin Hp Hq Himp.
assert (LE : forall l', (length (List.filter q l') <= length (List.filter p l'))%nat).
{ induction l' as [|a l' IH]; [simpl; lia|]. simpl. destruct (q a) eqn:Eq.
- rewrite (Himp a Eq). simpl. lia.
- destruct (p a); simpl; lia. }
induction l as [|a l IH]; [destruct Hin|]. destruct Hin as [E|Hin].
- subst a. simpl. rewrite Hp, Hq. simpl. pose proof (LE l). lia.
- specialize (IH Hin). simpl. destruct (q a) eqn:Eq.
+ rewrite (Himp a Eq). simpl. lia.
+ destruct (p a); simpl; lia.
Qed.

Lemma absent_set_lt : forall (k : reg) v R, bvmap_get k R = None -> (absent (bvmap_set k v R) < absent R)%nat.
Proof.
intros k v R H. unfold absent. apply (filter_length_lt (is_absent R) (is_absent (bvmap_set k v R)) keys5 k (keys5_all k)).
- unfold is_absent. rewrite H. reflexivity.
- unfold is_absent. rewrite bvmap_get_set_same. reflexivity.
- intros y Hy. unfold is_absent in *. destruct (bv_eqb k y) eqn:E.
+ apply bv_eqb_eq in E. subst y. rewrite bvmap_get_set_same in Hy. discriminate.
+ rewrite bvmap_get_set_other in Hy; [exact Hy|]. intros ->. rewrite bv_eqb_refl in E. discriminate.
Qed.

Definition tshape (R0 R : bvmap 5 word) : Prop := R = R0 \/ exists (k : reg) (v : word), is_x0 k = false /\ R = bvmap_set k v R0.
Definition fshape (F0 F : bvmap 5 word) : Prop := F = F0 \/ exists (k : reg) (v : word), F = bvmap_set k v F0.

Section Shape.
Variables R0 F0 : bvmap 5 word.

Definition sh (a b : bool) (c : core) : Prop :=
(if a then tshape R0 (c_regs c) else c_regs c = R0) /\ (if b then fshape F0 (c_fregs c) else c_fregs c = F0).

Lemma sh_base : forall a b pc fc rv, sh a b (Core R0 F0 pc fc rv).
Proof. intros [|] [|] pc fc rv; split; simpl; try reflexivity; left; reflexivity. Qed.

Local Ltac core_tac :=
unfold sh, rset, fset, with_regs, with_fregs, with_pc, with_fcsr, with_resv, accrue, fwrite, inval_resv in *; simpl in *.

Lemma sh_rset : forall b r v c, sh false b c -> sh true b (rset r v c).
Proof.
intros b r v [R F p f s] [H1 H2]. core_tac. subst R. destruct (is_x0 r) eqn:E; simpl; (split; [|exact H2]).
- left. reflexivity.
- right. exists r, v. split; [exact E| reflexivity].
Qed.
Lemma sh_fset : forall a r v c, sh a false c -> sh a true (fset r v c).
Proof. intros a r v [R F p f s] [H1 H2]. core_tac. subst F. split; [exact H1|]. right. exists r, v. reflexivity. Qed.
Lemma sh_fwrite : forall a fmt r v c, sh a false c -> sh a true (fwrite fmt r v c).
Proof. intros a fmt r v c H. destruct fmt; apply sh_fset; exact H. Qed.
Lemma sh_with_pc : forall a b v c, sh a b c -> sh a b (with_pc v c).
Proof. intros a b v [R F p f s] H. core_tac. exact H. Qed.
Lemma sh_with_fcsr : forall a b v c, sh a b c -> sh a b (with_fcsr v c).
Proof. intros a b v [R F p f s] H. core_tac. exact H. Qed.
Lemma sh_with_resv : forall a b v c, sh a b c -> sh a b (with_resv v c).
Proof. intros a b v [R F p f s] H. core_tac. exact H. Qed.
Lemma sh_accrue : forall a b fl c, sh a b c -> sh a b (accrue fl c).
Proof. intros a b fl [R F p f s] H. core_tac. exact H. Qed.
Lemma sh_inval_resv : forall a b x c, sh a b c -> sh a b (inval_resv x c).
Proof. intros a b x [R F p f s] H. core_tac. destruct s as [r|]; [destruct (Z.eqb _ _)|]; simpl; exact H. Qed.
Lemma sh_if : forall a b (t : bool) c1 c2, sh a b c1 -> sh a b c2 -> sh a b (if t then c1 else c2).
Proof. intros a b [] c1 c2 H1 H2; assumption. Qed.

Lemma sh_weak_r : forall b c, sh false b c -> sh true b c.
Proof. intros b c [H1 H2]. split; [left; exact H1| exact H2]. Qed.
Lemma sh_weak_f : forall a c, sh a false c -> sh a true c.
Proof. intros a c [H1 H2]. split; [exact H1| left; exact H2]. Qed.

Inductive eff_sh : eff -> Prop :=
| ShDone : forall c, sh true true c -> eff_sh (EDone c)
| ShIllegal : forall c, eff_sh (EIllegal c)
| ShEcall : forall c, eff_sh (EEcall c)
| ShEbreak : forall c, eff_sh (EEbreak c)
| ShFault : forall c, eff_sh (EFault c)
| ShDefIllegal : forall c, eff_sh (EDefinedIllegal c)
| ShLoad : forall n a k, (forall v, eff_sh (k v)) -> eff_sh (ELoad n a k)
| ShStore : forall n a v k, eff_sh k -> eff_sh (EStore n a v k).

Local Ltac solve_sh :=
repeat first [ apply sh_rset | apply sh_fset | apply sh_fwrite | apply sh_with_pc
| apply sh_with_fcsr | apply sh_with_resv | apply sh_accrue | apply sh_inval_resv | apply sh_if
| match goal with |- sh _ _ (match ?X with _ => _ end) => destruct X end ];
apply sh_base.

Local Ltac sh_struct :=
repeat first
[ apply ShDone; solve_sh
| apply ShIllegal | apply ShEcall | apply ShEbreak | apply ShFault | apply ShDefIllegal
| apply ShLoad; intros ?
| apply ShStore
| match goal with |- eff_sh (match ?X with _ => _ end) => destruct X end
| match goal with |- eff_sh (match ?X with _ => _ end _) => destruct X end ].

Local Ltac unfold_exec :=
cbv beta iota zeta delta [exec fget fread c_regs c_fregs c_pc c_fcsr c_resv
with_pc load_val store_val exec_csr resolve_rm frm_of].

Lemma exec_sh : forall pc fc rv sz i, eff_sh (exec sz i (Core R0 F0 pc fc rv)).
Proof.
intros pc fc rv sz i.
destruct i; unfold_exec; sh_struct.
Qed.
End Shape.

Section Step.
Variable segs : list Segment.

Lemma interp_sh : forall R0 F0 t, eff_sh R0 F0 t -> forall m r,
interp_eff_accesses segs t m = MachineOk r -> sh R0 F0 true true (fst (@access_value _ r)).
Proof.
intros R0 F0 t H. induction H as [c Hc|c|c|c|c|c|n a k Hk IH|n a v k Hk IH]; intros m r E; cbn [interp_eff_accesses] in E; try discriminate.
- injection E as <-. cbn. exact Hc.
- destruct (ov_read_bytes segs m a (width_bytes n)) as [bs|]; [|discriminate].
destruct (interp_eff_accesses segs (k (bv_extract 0 n (le_bytes_to_word bs))) m) as [r'| |] eqn:E'; try discriminate.
injection E as <-. cbn. exact (IH _ m r' E').
- destruct (store_ok segs m a (width_bytes n)); [|discriminate].
destruct (interp_eff_accesses segs k (write_to_mem m a (Z_to_le_bytes (width_bytes n) (bv_unsigned v)))) as [r'| |] eqn:E'; try discriminate.
injection E as <-. cbn. exact (IH _ r' E').
Qed.

Lemma decode_exec_sh : forall ms w r, decode_exec_accesses segs ms w = MachineOk r ->
tshape (ms_regs ms) (ms_regs (@access_value _ r)) /\ fshape (ms_fregs ms) (ms_fregs (@access_value _ r)).
Proof.
intros ms w r E. unfold decode_exec_accesses in E. destruct (is_ecall w).
{ injection E as <-. cbn. split; left; reflexivity. }
destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
match type of E with context [interp_eff_accesses segs ?t ?m] =>
destruct (interp_eff_accesses segs t m) as [rep| |] eqn:EI; try discriminate;
pose proof (interp_sh _ _ t (exec_sh (ms_regs ms) (ms_fregs ms) _ _ _ _ i) m rep EI) as [S1 S2] end.
destruct (@access_value _ rep) as [c m'] eqn:EV. injection E as <-. cbn in *. split; assumption.
Qed.

Lemma step_shape : forall ms ms', RiscvSemantics.step segs ms = MachineOk ms' ->
tshape (ms_regs ms) (ms_regs ms') /\ fshape (ms_fregs ms) (ms_fregs ms').
Proof.
intros ms ms' E. unfold RiscvSemantics.step, drop_access_report in E.
destruct (step_accesses segs ms) as [r| |] eqn:ES; try discriminate. injection E as <-.
unfold step_accesses in ES.
repeat match type of ES with
| context [match ?X with Some _ => _ | None => _ end] => destruct X
end; try (apply (decode_exec_sh _ _ _ ES)).
unfold fetch_failure in ES.
repeat match type of ES with context [if ?b then _ else _] => destruct b end; discriminate.
Qed.

Lemma is_x0_eqb : forall k : reg, is_x0 k = false -> bv_eqb k 0 = false.
Proof. intros k H. unfold is_x0 in H. unfold bv_eqb. exact H. Qed.

Lemma tshape_fix : forall R0 R Rc, tshape R0 R -> iregs_eqv Rc R0 -> iregs_eqv Rc R -> R = R0 \/ (absent R < absent R0)%nat.
Proof.
intros R0 R Rc [->|(k & v & Hk & ->)] E0 E1; [left; reflexivity|].
destruct (bvmap_get k R0) as [v'|] eqn:G; [left | right; apply absent_set_lt; exact G].
apply bvmap_set_same_id. rewrite G. f_equal.
pose proof (iregs_eqv_nz _ _ k E0 (is_x0_eqb k Hk)) as A0. pose proof (iregs_eqv_nz _ _ k E1 (is_x0_eqb k Hk)) as A1.
rewrite reg_get_set_same in A1. unfold reg_get in A0 at 2. rewrite G in A0. congruence.
Qed.
Lemma fshape_fix : forall F0 F Fc, fshape F0 F -> regs_eqv Fc F0 -> regs_eqv Fc F -> F = F0 \/ (absent F < absent F0)%nat.
Proof.
intros F0 F Fc [->|(k & v & ->)] E0 E1; [left; reflexivity|].
destruct (bvmap_get k F0) as [v'|] eqn:G; [left | right; apply absent_set_lt; exact G].
apply bvmap_set_same_id. rewrite G. f_equal.
pose proof (E0 k) as A0. pose proof (E1 k) as A1.
rewrite reg_get_set_same in A1. unfold reg_get in A0 at 2. rewrite G in A0. congruence.
Qed.

Lemma ms_eq_intro : forall a b : machine_state, ms_regs a = ms_regs b -> ms_fregs a = ms_fregs b -> ms_pc_val a = ms_pc_val b ->
ms_svc_pending a = ms_svc_pending b -> ms_resv a = ms_resv b -> ms_fcsr a = ms_fcsr b -> ms_mem a = ms_mem b -> ms_rom a = ms_rom b -> a = b.
Proof. intros [] []; simpl; intros; subst; reflexivity. Qed.

Lemma spin_fix : forall n msc mo mss,
(absent (ms_regs mss) + absent (ms_fregs mss) <= n)%nat -> ms_eqv msc mss -> ms_svc_pending msc = None ->
mi_account_step segs msc mo = MachineOk (msc, mo) -> QHWH.to_spin segs mss mo.
Proof.
induction n as [|n IH]; intros msc mo mss Hn Heqv Hsvc Hfix;
(pose proof (mi_account_step_eqv segs msc mss mo Heqv) as K; rewrite Hfix in K;
destruct (mi_account_step segs mss mo) as [[ms1 mo1]| |] eqn:E1; cbn in K; try contradiction; destruct K as [K1 <-];
pose proof (mi_account_step_projects segs mss mo ms1 mo E1) as ST; destruct (step_shape mss ms1 ST) as [SR SF];
pose proof Heqv as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8); pose proof K1 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8);
assert (Hsvc' : ms_svc_pending mss = None) by congruence;
destruct (tshape_fix _ _ _ SR H1 G1) as [ER|LR]; destruct (fshape_fix _ _ _ SF H2 G2) as [EF|LF];
try (assert (ms1 = mss) as -> by (apply ms_eq_intro; congruence); exact (QHWH.ts_spin segs mss mo Hsvc' E1))).
all: try (exfalso; rewrite ?ER, ?EF in *; lia).
all: apply (QHWH.ts_step segs mss mo ms1 mo Hsvc' E1); apply (IH msc mo ms1); [rewrite ?ER, ?EF in *; lia | exact K1 | exact Hsvc | exact Hfix].
Qed.

Theorem to_spin_eqv : forall ms mo, QHWH.to_spin segs ms mo -> forall ms', ms_eqv ms ms' -> QHWH.to_spin segs ms' mo.
Proof.
intros ms mo H. induction H as [ms mo Hsvc Hfix | ms mo ms1 mo1 Hsvc Hst _ IH]; intros ms' Heqv.
- exact (spin_fix _ ms mo ms' (le_n _) Heqv Hsvc Hfix).
- pose proof (mi_account_step_eqv segs ms ms' mo Heqv) as K. rewrite Hst in K.
destruct (mi_account_step segs ms' mo) as [[ms1' mo1']| |] eqn:E1; cbn in K; try contradiction. destruct K as [K1 <-].
destruct Heqv as (_ & _ & _ & H4 & _).
exact (QHWH.ts_step segs ms' mo ms1' mo1 ltac:(congruence) E1 (IH ms1' K1)).
Qed.

Notation cfg_eqv := (Qe4Y.cfg_eqv).

Theorem srealizes_eqv_mut :
(forall c T, Q1lV.srealizes segs c T -> forall c', cfg_eqv c c' -> Q1lV.srealizes segs c' T)
/\ (forall V T c, Q1lV.slbody segs V T c -> forall c', cfg_eqv c c' -> Q1lV.slbody segs (eclo V) T c').
Proof.
apply (Q1lV.srealizes_slbody_mutind segs
(fun c T _ => forall c', cfg_eqv c c' -> Q1lV.srealizes segs c' T)
(fun V T c _ => forall c', cfg_eqv c c' -> Q1lV.slbody segs (eclo V) T c')).
-  intros c I evs nx T i0 Hnode Hcont IH c' Heqv.
destruct (node_ok_tr segs c c' I evs nx Heqv Hnode) as [Hnode' Hnx].
apply (Q1lV.srz_node segs c' I evs (fun i => nx_tr segs c' (nx i)) T i0 Hnode'). intros i. apply (IH i). apply Hnx.
-  intros c Hh [ms' md'] [_ Hmd]. apply Q1lV.srz_halt. cbn in Hmd |- *. rewrite <- Hmd. exact Hh.
-  intros [ms md] Hs Hh [ms' md'] [Hms Hmd]. cbn in Hmd, Hs, Hh, Hms. subst md'.
apply Q1lV.srz_spin; cbn; [exact (to_spin_eqv ms md Hs ms' Hms)| exact Hh].
-  intros c T T' H IH Heq c' Heqv. eapply Q1lV.srz_conseq; [apply IH; exact Heqv| exact Heq].
-  intros V T c c_e HV Hbody IHbody Hstar He IHe c' Heqv.
destruct (star_eqv segs c [] c_e Hstar c' Heqv) as (c_e' & Hstar' & He').
apply (Q1lV.srz_loop segs (eclo V) T c' c_e').
+ exists c. split; [exact HV| exact Heqv].
+ intros c1 (c0 & HV0 & H01). exact (IHbody c0 HV0 c1 H01).
+ exact Hstar'.
+ apply IHe. exact He'.
-  intros V T c H IH c' Heqv. apply Q1lV.slb_exit. apply IH. exact Heqv.
-  intros V T c I nx k Hnode Hk IHk Hv c' Heqv.
destruct (node_ok_tr segs c c' I (fun _ => []) nx Heqv Hnode) as [Hnode' Hnx].
apply (Q1lV.slb_node segs (eclo V) T c' I (fun i => nx_tr segs c' (nx i)) k Hnode').
+ intros i Hi. apply (IHk i Hi). apply Hnx.
+ intros i Hi. exists (nx i). split; [exact (Hv i Hi)| apply Hnx].
Qed.

Theorem srealizes_eqv : forall c c' T, cfg_eqv c c' -> Q1lV.srealizes segs c T -> Q1lV.srealizes segs c' T.
Proof. intros c c' T Heqv H. exact (proj1 srealizes_eqv_mut c T H c' Heqv). Qed.

Theorem srealizes_canon : forall R F pc fc rv m ro md T,
Q1lV.srealizes segs (mkCfg (MS (canonR R) F pc fc rv m ro) md) T ->
Q1lV.srealizes segs (mkCfg (MS R F pc fc rv m ro) md) T.
Proof.
intros R F pc fc rv m ro md T H. eapply srealizes_eqv; [| exact H].
split; [| reflexivity]. apply ms_eqv_sym. apply ms_eqv_canon.
Qed.
End Step.
