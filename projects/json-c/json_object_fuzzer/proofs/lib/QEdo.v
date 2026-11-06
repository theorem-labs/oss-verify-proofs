(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC QgpE Q3bI QU0c Q85Z QJ4Q QND5 Qo8J QG64 QsSk QqZL Qt8n QWtD QOTP Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QWTC QgpE Q3bI QU0c Q85Z.Mq1 QJ4Q.Mq0 Q85Z QND5 Qo8J.Mq0 QG64 QsSk QqZL.Mq0.
Import Qt8n QWtD QqZL.Mq2 QOTP Q1LT.
Local Instance asanreflect_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope bv_scope.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac rif :=
repeat match goal with
| |- context [if bv_eqb ?a ?b then ?u else ?v] =>
lazymatch a with
| @BV _ _ _ =>
lazymatch b with
| @BV _ _ _ =>
let c := eval vm_compute in (bv_eqb a b) in
lazymatch c with
| true => change (if bv_eqb a b then u else v) with u
| false => change (if bv_eqb a b then u else v) with v
end
end
end
end.

Ltac pc_is v :=
lazymatch goal with
| |- msteps _ (mkst _ (Z_to_bv 64 ?q) _ _) _ => first [constr_eq q v | replace q with v by lia]
end.

Lemma len_eqb_sound : forall SEGS E M k n m,
know_ok SEGS E M k -> len_eqb k n m = true -> edenot E n = edenot E m.
Proof.
intros SEGS E M k n m HK H. unfold len_eqb in H. apply orb_prop in H as [H|H].
- apply expr_eqb_eq in H. subst. reflexivity.
- apply andb_prop in H as [H1 H2].
pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as A1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as A2.
cbn [xt_den] in A1, A2. apply bv_eq. lia.
Qed.

Lemma kwritable_sound : forall segs E M allkn k b off n,
know_ok segs E M allkn ->
know_ok segs E M k -> kwritable allkn k b off n = true -> 0 <= n ->
store_ok segs M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
/\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
Proof.
intros segs E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
apply Forall_cons_iff in HK as [HKK Hrest]. cbn [kwritable] in H.
destruct K; try exact (IH Hrest H).
lazymatch type of HKK with kentry_ok _ _ _ (KWr ?a ?n) => destruct a as [wb wk]; rename n into wn end.
cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
bv_unsigned (edenot E b) + off + n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true
/\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + n <= 2 ^ 64).
{ intros A B. split; [|lia].
replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
- destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hc0.
pose proof (xlo_sound segs E M allkn wn wl Hall Hx) as Hwl. unfold elenZ in *. apply CORE; lia.
- lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
destruct (xinside_sound segs E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u64_lit in I2 by lia.
unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. apply CORE; lia.
Qed.

Lemma kimg_cut_sound : forall segs E M k a n,
know_ok segs E M k -> know_ok segs E M (kimg_cut k a n).
Proof.
intros segs E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
lazymatch goal with |- Forall _ (if _ then [KImg ?a ?b] else _) => rename a into lo; rename b into hi end.
destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Hnone).
apply Forall_app. split.
- destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
- destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.

Lemma reg_lit5 : forall n, (n < 32)%nat -> bv_unsigned (Z_to_bv 5 (Z.of_nat n)) = Z.of_nat n.
Proof.
intros n Hn. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. apply Z.mod_small. lia.
Qed.

Lemma regs_ok_post2 : forall E sr R R' n1 (r1 : bv 5) e1 n2 (r2 : bv 5) e2,
regs_ok E sr R -> (0 < n1 < 32)%nat -> (0 < n2 < 32)%nat -> n1 <> n2 ->
bv_unsigned r1 = Z.of_nat n1 -> bv_unsigned r2 = Z.of_nat n2 ->
getr R' r1 = edenot E e1 -> getr R' r2 = edenot E e2 ->
(forall r, r <> r1 -> r <> r2 -> getr R' r = getr R r) ->
regs_ok E (sr_upd (sr_upd sr n1 e1) n2 e2) R'.
Proof.
intros E sr R R' n1 r1 e1 n2 r2 e2 HR Hn1 Hn2 Hne U1 U2 G1 G2 Gr.
assert (E1 : r1 = Z_to_bv 5 (Z.of_nat n1)) by (apply bv_eq; rewrite reg_lit5 by lia; exact U1).
assert (E2 : r2 = Z_to_bv 5 (Z.of_nat n2)) by (apply bv_eq; rewrite reg_lit5 by lia; exact U2).
pose proof (regs_ok_set_n E _ _ n2 e2 (edenot E e2) (regs_ok_set_n E sr R n1 e1 (edenot E e1) HR Hn1 eq_refl) Hn2 eq_refl) as K.
rewrite <- E1, <- E2 in K.
assert (Z1 : r1 <> 0%bv) by (intros H0; apply (f_equal bv_unsigned) in H0; rewrite U1 in H0; change (bv_unsigned (0%bv : bv 5)) with 0 in H0; lia).
assert (Z2 : r2 <> 0%bv) by (intros H0; apply (f_equal bv_unsigned) in H0; rewrite U2 in H0; change (bv_unsigned (0%bv : bv 5)) with 0 in H0; lia).
assert (Z12 : r1 <> r2) by (intros H0; apply (f_equal bv_unsigned) in H0; lia).
intros r. rewrite <- (K r).
destruct (bv_eqb r r2) eqn:Q2.
{ unfold bv_eqb in Q2. apply Z.eqb_eq in Q2. apply bv_eq in Q2. subst r. rewrite getr_same by exact Z2. exact G2. }
assert (N2 : r <> r2) by (intros ->; rewrite bv_eqb_refl in Q2; discriminate).
rewrite (getr_other _ r2 _ r N2).
destruct (bv_eqb r r1) eqn:Q1.
{ unfold bv_eqb in Q1. apply Z.eqb_eq in Q1. apply bv_eq in Q1. subst r. rewrite getr_same by exact Z1. exact G1. }
assert (N1 : r <> r1) by (intros ->; rewrite bv_eqb_refl in Q1; discriminate).
rewrite (getr_other _ r1 _ r N1). apply Gr; assumption.
Qed.

Fixpoint nb_lt (b : nat) (e : expr) : bool :=
match e with
| ELit _ => true
| EVar n => Nat.ltb n b
| EAlu _ a c | EAluw _ a c | EMd _ a c | EMdw _ a c => nb_lt b a && nb_lt b c
| EExt _ _ _ a => nb_lt b a
| EBlob _ _ _ _ => false
end.

Lemma edenot_ev_agree : forall b E E' e,
nb_lt b e = true -> (forall n, (n < b)%nat -> ev E n = ev E' n) -> edenot E e = edenot E' e.
Proof.
intros b E E' e. induction e; cbn [nb_lt edenot]; intros H Hag; try reflexivity;
try (apply andb_prop in H as [H1 H2]; rewrite (IHe1 H1 Hag), (IHe2 H2 Hag); reflexivity).
- apply Hag. apply Nat.ltb_lt. exact H.
- rewrite (IHe H Hag). reflexivity.
- discriminate.
Qed.

Lemma fetch_lit : forall segs z (w : word) x,
bv_unsigned w = z -> fetch_word segs w = Some x -> fetch_word segs (Z_to_bv 64 z) = Some x.
Proof.
intros segs z w x Hw Hf. replace (Z_to_bv 64 z) with w; [exact Hf|].
apply bv_eq. rewrite Z_to_bv_unsigned, <- Hw. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma with_ss_idem : forall cs s1 s2, with_ss (with_ss cs s1) s2 = with_ss cs s2.
Proof. reflexivity. Qed.
Lemma a_ss_with_ss : forall cs s, a_ss (with_ss cs s) = s.
Proof. reflexivity. Qed.

Lemma page_base_le' : forall a : word, bv_unsigned (page_base a) <= bv_unsigned a
/\ bv_unsigned a < bv_unsigned (page_base a) + 4096
/\ bv_unsigned (page_base a) mod 4096 = 0.
Proof.
intros a. unfold page_base, page_base_of, page_size. pose proof (u64_range a) as Ha.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
assert (H : 0 <= bv_unsigned a / 4096 * 4096 <= bv_unsigned a) by lia.
rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma A_wf_allowA' : forall A E cs, A_wf (allowA A E cs).
Proof.
intros A E cs. unfold A_wf, allowA. apply Forall_forall. intros iv Hin.
apply in_flat_map in Hin as [p [_ Hin]]. unfold allow1 in Hin.
pose proof (u64_range (edenot E (snd p))) as Hn. pose proof (u64_range (edenot E (fst p))) as Hb.
destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; unfold page_size.
- pose proof (pagedown_le (uE E (fst p))). pose proof (pageup_ge (uE E (fst p) + uE E (snd p))). unfold uE in *.
split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
- pose proof (pagedown_le (sh_lo A E p)). pose proof (pageup_ge (sh_hi A E p)). unfold sh_lo, sh_hi, uE in *.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
split; [lia|]. split; [apply pagedown_mod | apply pageup_mod].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Section NodesD.

Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable USP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
#[local] Notation ATOP := (APS.ATOP USP).
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

Definition Hv (E : env) (cs : acs) (model : Model) : word -> bool := fun a => negb (vis A USP E cs model a).

Lemma Hv_high : forall E cs model (a : word), ATOP <= bv_unsigned a -> Hv E cs model a = false.
Proof.
intros E cs model a Ha. unfold Hv, vis. apply negb_false_iff.
replace (ATOP <=? bv_unsigned a) with true by (symmetry; apply Z.leb_le; exact Ha).
rewrite orb_true_r. reflexivity.
Qed.

Lemma lazy_cover_vis : forall E cs R FULL model,
cs_ok SEGS A LIMIT USP SINV argH FS0 E cs R FULL model -> lazy_cover (Hv E cs model) (m_vm_lazy model) (allowA A E cs).
Proof.
intros E cs R FULL model HC w Hlz Hh. unfold Hv in Hh.
apply negb_false_iff in Hh. unfold vis in Hh. rename Hh into Hv0.
pose proof (APS.page_in_ranges_apart A (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) 0%nat w _ _ (co_lazyb _ _ _ _ _ _ _ _ _ _ _ _ HC) Hlz) as [B1 B2].
pose proof HULL_ok as HU; unfold hull_ok in HU; destruct HU as (H0 & H1 & H2 & H3).
apply orb_prop in Hv0 as [Hv0|Hv0].
- apply orb_prop in Hv0 as [Hv0|Hv0].
+ congruence.
+ apply Z.leb_le in Hv0. lia.
- apply andb_prop in Hv0 as [_ Hv0]. rewrite Hlz in Hv0. cbn [negb orb] in Hv0.
pose proof (page_base_le' w) as (P1 & P2 & P3).
unfold page_allowedb, allowA. apply existsb_exists. unfold page_size.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
unfold in_allow in Hv0. apply orb_prop in Hv0 as [Hv0|Hv0].
+ unfold in_vis in Hv0. apply existsb_exists in Hv0 as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
exists (pagedown (uE E (fst p)), pageup (uE E (fst p) + uE E (snd p))). split.
* apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. left. reflexivity.
* cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
+ unfold in_sh in Hv0. apply existsb_exists in Hv0 as [p [Hin Hb]]. apply andb_prop in Hb as [Hb1 Hb2].
apply Z.leb_le in Hb1. apply Z.ltb_lt in Hb2.
exists (pagedown (sh_lo A E p), pageup (sh_hi A E p)). split.
* apply in_flat_map. exists p. split; [apply in_or_app; left; exact Hin|]. right. left. reflexivity.
* cbn [fst snd]. apply andb_true_intro. split; apply Z.leb_le; unfold pagedown, pageup; lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma H_off_segments_vis : forall E cs model, H_off_segments SEGS (Hv E cs model).
Proof.
intros E cs model a Hh. unfold Hv in Hh. apply negb_true_iff in Hh. unfold vis in Hh.
apply orb_false_iff in Hh as [Hh _]. apply orb_false_iff in Hh as [Hh _].
apply SEGS_in_hull. exact Hh.
Qed.

Lemma mrestrict_Hv_high : forall E cs model FULL (a : word),
ATOP <= bv_unsigned a -> mrestrict (Hv E cs model) FULL a = FULL a.
Proof. intros. unfold mrestrict. rewrite Hv_high by assumption. reflexivity. Qed.

Lemma Mr_grows_Hv : forall E cs model FULL,
mem_grows (Mr A USP argH E cs model FULL) (mrestrict (Hv E cs model) FULL).
Proof.
intros E cs model FULL a. unfold Mr, mrestrict, hid, Hv.
destruct (argH E a), (vis A USP E cs model a); cbn; auto.
Qed.

Lemma munrestrict_mrestrict : forall (H : word -> bool) FULL, munrestrict H FULL (mrestrict H FULL) = FULL.
Proof.
intros H FULL. apply functional_extensionality. intros a. unfold munrestrict, mrestrict. destruct (H a); reflexivity.
Qed.

End NodesD.
End Mq0.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6EJ QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import QWTC Q85Z Q6EJ QND5 QsSk QqZL.Mq0 Qt8n QWtD QqZL.Mq2 QDlz QOTP Q1LT.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

Section Iface.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable USP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

Definition OBL_mmap2 : Prop := mm2_stmt SEGS A nx0 LIMIT USP SINV argH FS0 (node_mmap2 A nx0 LIMIT).
Definition OBL_mmapin : Prop := forall hole : bool, mm3_stmt SEGS A nx0 LIMIT USP SINV argH FS0 (node_mmapin A LIMIT hole).
Definition OBL_mprotect2 : Prop := mm2_stmt SEGS A nx0 LIMIT USP SINV argH FS0 (node_mprotect2 A LIMIT).
Definition OBL_brk2 : Prop := brk2_stmt SEGS A nx0 LIMIT USP SINV argH FS0.
Definition OBL_brk2u : Prop := brk2u_stmt SEGS A nx0 LIMIT USP SINV argH FS0.
Definition OBL_sys : Prop := forall y : snode, sys_stmt SEGS A nx0 LIMIT USP SINV argH FS0 y.
Definition OBL_exit : Prop := exit_stmt SEGS A LIMIT USP SINV argH FS0.

Definition OBL_all : Prop := OBL_mmap2 /\ OBL_mmapin /\ OBL_mprotect2 /\ OBL_brk2 /\ OBL_brk2u /\ OBL_sys /\ OBL_exit.

End Iface.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QWTC Q85Z.Mq1 Q85Z QND5 QsSk QqZL.Mq0 Qt8n QWtD QqZL.Mq2 QOTP Q1LT.
Import ListNotations. Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
Import AX2. Import AX2S. Import AP. Import APS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Lemma bytes_le_to_Z_cons : forall (b : byte) bs,
bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite <- Z.lxor_lor.
- rewrite Z.add_nocarry_lxor; [reflexivity|].
apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
+ change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
+ rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
- apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
+ change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
+ rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|].
cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons.
pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by lia. exact IH.
Qed.

Section Sound2.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable USP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

Lemma kread_bytes_sound : forall E M k n b off zs,
know_ok SEGS E M k ->
kread_bytes SEGS n k b off = Some zs ->
0 <= estart E (SA b off) -> estart E (SA b off) + Z.of_nat n <= 2 ^ 64 ->
exists bs, length bs = n /\ map bv_unsigned bs = zs
/\ forall j, (j < n)%nat -> rdn SEGS M (Z_to_bv 64 (estart E (SA b off) + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
intros E M k n. induction n as [|n IH]; intros b off zs HK Hr Hlo Hhi.
- cbn in Hr. injection Hr as <-. exists []. repeat split; try reflexivity. intros j Hj. lia.
- cbn [kread_bytes] in Hr.
destruct (kreadZ SEGS k b off 1) as [z|] eqn:Hz; [|discriminate].
destruct (kread_bytes SEGS n k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate]. injection Hr as <-.
unfold kreadZ in Hz.
pose proof (know_lookup_sound SEGS E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as KL.
destruct (know_lookup SEGS k b off 1 false [] []) as [v scs nx| |]; try discriminate.
destruct v as [zl| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection Hz as <-.
assert (Hfl : flat E (SA b off) (Z.of_nat 1)) by (unfold flat; change (Z.of_nat 1) with 1; rewrite Nat2Z.inj_succ in Hhi; lia).
destruct (KL ltac:(constructor) Hfl) as [bs1 (R1 & L1 & V1)].
destruct bs1 as [|b0 [|? ?]]; try (cbn in L1; lia).
destruct (IH b (off + 1) rest HK Hrest) as [bs (Lb & Mb & Rb)].
{ unfold estart in *; cbn [a_base a_off] in *. lia. }
{ unfold estart in *; cbn [a_base a_off] in *. rewrite Nat2Z.inj_succ in Hhi. lia. }
exists (b0 :: bs). split; [cbn; lia|]. split.
+ cbn [map]. rewrite Mb. f_equal.
cbn [edenot] in V1. apply (f_equal bv_unsigned) in V1. rewrite !u_lit64 in V1.
unfold extz in V1. cbn [bytes_le_to_Z] in V1. rewrite Z.shiftl_0_l, Z.lor_0_r in V1.
pose proof (u8_range b0). unfold two64 in *. rewrite Z.mod_small in V1 by lia. exact V1.
+ intros j Hj. destruct j as [|j].
* cbn [nth]. change (Z.of_nat 0) with 0. rewrite Z.add_0_r. rewrite <- R1. reflexivity.
* cbn [nth]. rewrite <- (Rb j) by lia. f_equal. f_equal. unfold estart; cbn [a_base a_off]. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma rdn_of_bytes1 : forall M n (a : word) bs,
length bs = n -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
(forall j, (j < n)%nat -> rdn SEGS M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)]) ->
rdn SEGS M a n = Some bs.
Proof.
intros M n. induction n as [|n IH]; intros a bs Hlen Hnw Hpt.
- destruct bs; [reflexivity | cbn in Hlen; lia].
- destruct bs as [|b bs']; [cbn in Hlen; lia|]. cbn in Hlen.
pose proof (Hpt 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [nth] in H0.
destruct n as [|n'].
+ destruct bs'; [exact H0 | cbn in Hlen; lia].
+ apply rdn_cons1; [exact H0|].
assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
apply IH; [lia | rewrite Hu1; lia |].
intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
exact (Hpt (S j) ltac:(lia)).
Qed.

Theorem node_join_sound : join_stmt SEGS A nx0 LIMIT USP SINV argH FS0.
Proof.
intros b off n cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold node_join in Hn.
destruct (Nat.leb 1 n && Nat.leb n 8 && flat_x (kn cs) b off (ELit (Z.of_nat n)))%bool eqn:Ht; [|discriminate].
apply andb_prop in Ht as [Ht Hfx]. apply andb_prop in Ht as [H1 H8]. apply Nat.leb_le in H1. apply Nat.leb_le in H8.
destruct (kread_bytes SEGS n (kn cs) b off) as [zs|] eqn:Hr; [|discriminate].
apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbn in Hn. subst cs'.
pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
pose proof (flat_x_sound SEGS E _ (kn cs) b off (ELit (Z.of_nat n)) HK Hfx) as (F1 & F2 & F3).
rewrite edenot_lit, u64_lit in F2, F3 by lia.
destruct (kread_bytes_sound E _ (kn cs) n b off zs HK Hr F1 F2) as [bs (Lb & Mb & Rb)].
apply (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _))); [|reflexivity].
unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT USP SINV argH FS0); [exact HC|]. constructor; [|exact HK].
cbn [kentry_ok]. split; [exact H8|]. split; [unfold flat; lia|].
rewrite (rdn_of_bytes1 _ n (adenot E (SA b off)) bs Lb).
- f_equal. cbn [edenot]. unfold word_to_le_bytes. rewrite <- Mb, zbytes_map.
pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Lb in Bb.
assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
rewrite u64_lit by lia. rewrite <- Lb. symmetry. apply Z_to_le_bytes_to_Z.
- rewrite (flat_u E _ (Z.of_nat n)); [lia | unfold flat; lia].
- intros j Hj. rewrite (flat_u E _ (Z.of_nat n)) by (unfold flat; lia). exact (Rb j Hj).
Qed.
End Sound2.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Logic.FunctionalExtensionality.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import QWTC QgpE Q3bI QU0c Q85Z.Mq1 Q85Z QND5 QsSk QqZL.Mq0 Q6EJ Qo8J.Mq0.
Import Qt8n QWtD QqZL.Mq2 QDlz QOTP Q1LT.
Import QqZL.Mq1.
Local Instance asanreflect_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope Z_scope.

Module APSX.
Import AX2. Import AX2S. Import AP. Import APS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition kept_ok (regs regs' : bvmap 5 word) : Prop :=
forall r : bv 5, r <> 0%bv -> ~ In (ridx r) caller_saved -> getr regs' r = getr regs r.

Section Specs.
Variable SEGS : list Segment.

Definition fill_spec (entry cmax : Z) : Prop :=
forall mem0 (s c : word) (n : Z) (regs : bvmap 5 word) (ret : word),
0 <= n -> bv_unsigned s + n < 2 ^ 64 ->
store_ok SEGS mem0 s (Z.to_nat n) = true ->
bv_unsigned c < cmax ->
ret_ok ret -> getr regs 1%bv = ret ->
getr regs 10%bv = s -> getr regs 11%bv = c -> getr regs 12%bv = Z_to_bv 64 n ->
exists regs',
msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
(mkst regs' ret (wbytes mem0 s (repeat (Z_to_bv 8 (bv_unsigned c)) (Z.to_nat n))) (seg_rom SEGS))
/\ kept_ok regs regs' /\ getr regs' 10%bv = s.

Definition copy_spec (entry : Z) : Prop :=
forall mem0 (dst src : word) (n : Z) (bs : list byte) (regs : bvmap 5 word) (ret : word),
0 <= n -> length bs = Z.to_nat n ->
rdn SEGS mem0 src (length bs) = Some bs ->
store_ok SEGS mem0 dst (length bs) = true ->
(bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst) ->
bv_unsigned src + n < 2 ^ 64 -> bv_unsigned dst + n < 2 ^ 64 ->
ret_ok ret -> getr regs 1%bv = ret ->
getr regs 10%bv = dst -> getr regs 11%bv = src -> getr regs 12%bv = Z_to_bv 64 n ->
exists regs',
msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
(mkst regs' ret (wbytes mem0 dst bs) (seg_rom SEGS))
/\ kept_ok regs regs' /\ getr regs' 10%bv = dst.

Definition miz_spec (entry : Z) : Prop :=
forall mem (beg sp : word) (N : Z) (regs : bvmap 5 word) (ret : word),
0 <= N <= 2 ^ 40 -> bv_unsigned beg + N + 8 <= 2 ^ 64 -> 16 <= bv_unsigned sp ->
store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 8)) 8 = true ->
(bv_unsigned beg + N <= bv_unsigned sp - 8 \/ bv_unsigned sp <= bv_unsigned beg) ->
(forall a : word, bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N ->
rdn SEGS mem a 1 = Some [Z_to_bv 8 0]) ->
ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp ->
getr regs 10%bv = beg -> getr regs 11%bv = Z_to_bv 64 N ->
exists regs',
msteps SEGS (mkst regs (Z_to_bv 64 entry) mem (seg_rom SEGS))
(mkst regs' ret (wbytes mem (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ret)) (seg_rom SEGS))
/\ kept_ok regs regs' /\ getr regs' 10%bv = Z_to_bv 64 1.

Definition SEALED_BYTES : list byte :=
[Z_to_bv 8 0x3c; Z_to_bv 8 0x73; Z_to_bv 8 0x65; Z_to_bv 8 0x61; Z_to_bv 8 0x6c; Z_to_bv 8 0x65; Z_to_bv 8 0x64; Z_to_bv 8 0x3e]
++ repeat (Z_to_bv 8 0) 4087.

Definition istrncpy_spec (entry src : Z) : Prop :=
forall mem0 (dst : word) (regs : bvmap 5 word) (ret : word),
(forall i, src <= i < src + 9 -> mem0 (Z_to_bv 64 i) = None) ->
store_ok SEGS mem0 dst 4095%nat = true ->
bv_unsigned dst + 4095 < 2 ^ 64 ->
(bv_unsigned dst + 4095 <= src \/ src + 9 <= bv_unsigned dst) ->
ret_ok ret -> getr regs 1%bv = ret ->
getr regs 10%bv = dst -> getr regs 11%bv = Z_to_bv 64 src -> getr regs 12%bv = Z_to_bv 64 4095 ->
exists regs',
msteps SEGS (mkst regs (Z_to_bv 64 entry) mem0 (seg_rom SEGS))
(mkst regs' ret (wbytes mem0 dst SEALED_BYTES) (seg_rom SEGS))
/\ kept_ok regs regs' /\ getr regs' 10%bv = dst.

End Specs.

Lemma reg_of_ridx : forall (r : bv 5) n, ridx r = n -> r = Z_to_bv 5 (Z.of_nat n).
Proof.
intros r n H. unfold ridx in H. apply bv_eq. rewrite Z_to_bv_unsigned.
pose proof (bv_unsigned_in_range _ r) as Hr. change (bv_modulus 5) with 32%Z in Hr.
unfold bv_wrap. change (bv_modulus 5) with 32%Z. rewrite Z.mod_small by lia. lia.
Qed.

Lemma regs_ok_pointwise : forall E sr R,
(forall r : bv 5, r <> 0%bv -> getr R r = edenot E (nth (ridx r) sr (ELit 0))) -> regs_ok E sr R.
Proof.
intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
- assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; apply Z.eqb_eq in Hr0; exact Hr0). subst r.
cbn [edenot]. apply getr_zero.
- apply H. intros X. subst r. unfold bv_eqb in Hr0. rewrite Z.eqb_refl in Hr0. discriminate.
Qed.

Lemma caller_saved_nodup : List.NoDup caller_saved.
Proof.
unfold caller_saved.
repeat (apply List.NoDup_cons; [cbn; intros H; repeat (destruct H as [H|H]; [lia|]); exact H|]). apply List.NoDup_nil.
Qed.

Lemma nth_sr_fresh_out : forall cs0 nx sr i,
~ In i cs0 -> nth i (sr_fresh sr cs0 nx) (ELit 0) = nth i sr (ELit 0).
Proof.
intros cs0. induction cs0 as [|c t IH]; intros nx sr i Hn; cbn [sr_fresh]; [reflexivity|].
rewrite IH by (intros X; apply Hn; right; exact X). rewrite nth_sr_upd.
destruct (Nat.eqb_spec i c) as [->|]; [exfalso; apply Hn; left; reflexivity | reflexivity].
Qed.

Lemma nth_sr_fresh_in : forall cs0 nx sr j,
List.NoDup cs0 -> (j < length cs0)%nat -> nth (nth j cs0 0%nat) (sr_fresh sr cs0 nx) (ELit 0) = EVar (nx + j).
Proof.
intros cs0. induction cs0 as [|c t IH]; intros nx sr j Hnd Hj; cbn [length] in Hj; [lia|].
inversion Hnd as [|c' t' Hnotin Hnd']; subst.
cbn [sr_fresh]. destruct j as [|j].
- cbn [nth]. rewrite nth_sr_fresh_out by exact Hnotin. rewrite nth_sr_upd, Nat.eqb_refl. f_equal. lia.
- cbn [nth]. rewrite IH by (assumption || lia). f_equal. lia.
Qed.

Definition ext_call (E : env) (nx : nat) (R' : bvmap 5 word) : env :=
Env (fun n => if (Nat.leb nx n && Nat.ltb n (nx + NCS))%bool
then getr R' (Z_to_bv 5 (Z.of_nat (nth (n - nx) caller_saved 0%nat)))
else ev E n) (eb E).

Lemma ext_call_agree : forall E nx R', env_agree nx E (ext_call E nx R').
Proof.
intros E nx R'. split; [|reflexivity]. intros n Hn. cbn [ext_call ev].
destruct (Nat.leb_spec nx n); [lia|]. reflexivity.
Qed.

Lemma ext_call_var : forall E nx R' j, (j < NCS)%nat ->
ev (ext_call E nx R') (nx + j) = getr R' (Z_to_bv 5 (Z.of_nat (nth j caller_saved 0%nat))).
Proof.
intros E nx R' j Hj. cbn [ext_call ev].
replace (Nat.leb nx (nx + j) && Nat.ltb (nx + j) (nx + NCS))%bool with true.
2:{ symmetry. apply andb_true_intro. split; [apply Nat.leb_le; lia | apply Nat.ltb_lt; lia]. }
f_equal. f_equal. f_equal. f_equal. lia.
Qed.

Lemma nth_sr_vars_lt' : forall b sr r, AP.sr_vars_lt b sr = true -> (r < 32)%nat -> AP.expr_vars_lt b (nth r sr (ELit 0)) = true.
Proof.
intros b sr. induction sr as [|x t IH]; intros r H Hr; [destruct r; reflexivity|].
cbn [AP.sr_vars_lt] in H. apply andb_prop in H as [H1 H2]. destruct r as [|r]; [exact H1|]. cbn [nth]. apply IH; [exact H2 | lia].
Qed.

Lemma regs_after_call : forall E sr R R' nx rv,
regs_ok E sr R -> AP.sr_vars_lt nx sr = true -> kept_ok R R' ->
match rv with Some e => AP.expr_vars_lt nx e = true /\ getr R' (Z_to_bv 5 10) = edenot E e | None => True end ->
regs_ok (ext_call E nx R')
(match rv with Some e => sr_upd (sr_fresh sr caller_saved nx) 10 e | None => sr_fresh sr caller_saved nx end) R'.
Proof.
intros E sr R R' nx rv HR Hsv Hkept Hrv.
pose proof (ext_call_agree E nx R') as Hag.
assert (OLD : forall i, (i < 32)%nat -> edenot (ext_call E nx R') (nth i sr (ELit 0)) = edenot E (nth i sr (ELit 0))).
{ intros i Hi. symmetry. apply (edenot_agree' nx); [exact Hag|]. apply nth_sr_vars_lt'; assumption. }
apply regs_ok_pointwise. intros r Hr0.
assert (CASES : forall i, (i < 32)%nat -> In i caller_saved \/ ~ In i caller_saved).
{ intros i _. destruct (in_dec Nat.eq_dec i caller_saved); auto. }
pose proof (ridx_range r) as Hrr.
assert (GEN : getr R' r = edenot (ext_call E nx R') (nth (ridx r) (sr_fresh sr caller_saved nx) (ELit 0))).
{ destruct (CASES (ridx r) Hrr) as [Hin|Hnin].
- destruct (In_nth caller_saved (ridx r) 0%nat Hin) as (j & Hj & Hnth).
rewrite <- Hnth at 1. rewrite nth_sr_fresh_in by (apply caller_saved_nodup || exact Hj).
cbn [edenot]. rewrite ext_call_var by exact Hj. rewrite Hnth. rewrite <- (reg_of_ridx r _ eq_refl). reflexivity.
- rewrite nth_sr_fresh_out by exact Hnin. rewrite OLD by exact Hrr.
rewrite (Hkept r Hr0 Hnin). pose proof (HR r) as X. unfold sr_get in X.
destruct (bv_eqb r 0) eqn:Hb; [exfalso; apply Hr0; apply bv_eq; unfold bv_eqb in Hb; apply Z.eqb_eq in Hb; exact Hb|].
exact X. }
destruct rv as [e|]; [|exact GEN].
destruct Hrv as [Hev Ha0]. rewrite nth_sr_upd.
destruct (Nat.eqb_spec (ridx r) 10) as [H10|H10]; [|exact GEN].
rewrite (reg_of_ridx r 10 H10). change (Z.of_nat 10) with 10%Z.
rewrite Ha0. apply (edenot_agree' nx); [exact Hag | exact Hev].
Qed.

Lemma wbytes_same : forall bs m (a : word),
bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 ->
(forall j, (j < length bs)%nat -> m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = Some (nth j bs (Z_to_bv 8 0))) ->
wbytes m a bs = m.
Proof.
intros bs m a Hnw Hall. apply functional_extensionality. intros x.
pose proof (u64_range x) as Hx.
destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a)) as [Hlt|Hge].
{ apply wbytes_out; [exact Hnw | lia]. }
destruct (Z_lt_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [Hin|Hout].
2: { apply wbytes_out; [exact Hnw | lia]. }
set (j := Z.to_nat (bv_unsigned x - bv_unsigned a)).
assert (Hxj : x = Z_to_bv 64 (bv_unsigned a + Z.of_nat j)).
{ subst j. rewrite Z2Nat.id by lia. replace (bv_unsigned a + (bv_unsigned x - bv_unsigned a)) with (bv_unsigned x) by lia.
symmetry. apply Z_to_bv_bv_unsigned. }
rewrite Hxj at 1. rewrite wbytes_nth by lia. rewrite Hxj. symmetry. apply Hall. lia.
Qed.

Lemma wbytes_defined : forall bs m (a : word) j,
bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64 -> (j < length bs)%nat ->
wbytes m a bs (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None.
Proof. intros bs m a j Hnw Hj. rewrite wbytes_nth by assumption. discriminate. Qed.

Lemma rdn_overlay_all : forall segs m n (a : word) b,
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
(forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (bv_unsigned a + i)) = Some b) ->
rdn segs m a n = Some (repeat b n).
Proof.
intros segs m n; induction n as [|n IH]; intros a b Hnw Hall; [reflexivity|].
cbn [rdn repeat].
pose proof (Hall 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
destruct n as [|n'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
rewrite (IH (a + 1)%bv b); [reflexivity | rewrite Hu1; lia |].
intros i Hi. rewrite Hu1. replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia. apply Hall. lia.
Qed.

Lemma rdn1_overlay : forall segs m (a : word) b, m a = Some b -> rdn segs m a 1 = Some [b].
Proof. intros segs m a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Lemma rdn_nth : forall segs m n (a : word) bs j,
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
rdn segs m a n = Some bs -> (j < n)%nat ->
rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
Proof.
intros segs m n; induction n as [|n IH]; intros a bs j Hnw H Hj; [lia|].
cbn [rdn] in H.
destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|] eqn:Hb0; [|discriminate].
destruct (rdn segs m (a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate]. injection H as <-.
destruct j as [|j'].
- cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. cbn [rdn]. rewrite Hb0. reflexivity.
- cbn [nth]. destruct n as [|n'']; [lia|].
assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
replace (bv_unsigned a + Z.of_nat (S j')) with (bv_unsigned (a + 1)%bv + Z.of_nat j') by lia.
apply (IH (a + 1)%bv rest j'); [lia | exact Hrest | lia].
Qed.

Lemma rdn_of_nth : forall segs m n (a : word) (f : nat -> byte),
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
(forall j, (j < n)%nat -> rdn segs m (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) 1 = Some [f j]) ->
rdn segs m a n = Some (map f (seq 0 n)).
Proof.
intros segs m n; induction n as [|n IH]; intros a f Hnw Hall; [reflexivity|].
cbn [rdn seq map].
pose proof (Hall 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. cbn [rdn] in H0.
destruct (match m a with Some b0 => Some b0 | None => seg_rom segs a end) as [b0|]; [|discriminate].
injection H0 as ->.
destruct n as [|n'].
- reflexivity.
- assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
rewrite (IH (a + 1)%bv (fun j => f (S j))); [rewrite <- seq_shift, map_map; reflexivity | lia |].
intros j Hj. rewrite Hu1. replace (bv_unsigned a + 1 + Z.of_nat j) with (bv_unsigned a + Z.of_nat (S j)) by lia.
apply Hall. lia.
Qed.

Lemma land_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
Z.land (a * 2 ^ k) b = 0%Z.
Proof.
intros a b k Ha Hk Hb. apply Z.bits_inj'. intros i Hi.
rewrite Z.land_spec, Z.bits_0.
destruct (Z.lt_ge_cases i k) as [Hl|Hh].
- rewrite Z.mul_pow2_bits_low by lia. reflexivity.
- rewrite (Z_testbit_high k b i) by lia. apply Bool.andb_false_r.
Qed.

Lemma lor_shl_disjoint : forall a b k, (0 <= a)%Z -> (0 <= k)%Z -> (0 <= b < 2 ^ k)%Z ->
Z.lor (a * 2 ^ k) b = (a * 2 ^ k + b)%Z.
Proof.
intros a b k Ha Hk Hb.
rewrite <- Z.lxor_lor by (apply land_shl_disjoint; lia).
symmetry. apply Z.add_nocarry_lxor. apply land_shl_disjoint; lia.
Qed.

Lemma Z_to_le_bytes_of_bytes : forall bs,
Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b rest IH]; [reflexivity|].
cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256%Z in Hb.
pose proof (bytes_le_to_Z_nonneg rest) as Hr.
assert (Hlor : Z.lor (bv_unsigned b) (Z.shiftl (bytes_le_to_Z rest) 8) = bv_unsigned b + 2 ^ 8 * bytes_le_to_Z rest).
{ rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.lor_comm. rewrite lor_shl_disjoint by lia. lia. }
rewrite Hlor. f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2 ^ 8).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
change (2 ^ 8) with 256 in *. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256 in *.
replace ((bv_unsigned b + 256 * bytes_le_to_Z rest) / 256) with (bytes_le_to_Z rest) by lia. exact IH.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

Lemma word_to_le_bytes_of_bytes : forall bs,
(length bs <= 8)%nat ->
word_to_le_bytes (length bs) (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
intros bs Hlen. unfold word_to_le_bytes.
pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb.
assert (Hlt : bytes_le_to_Z bs < 2 ^ 64).
{ eapply Z.lt_le_trans; [exact (proj2 Hb)|]. apply Z.pow_le_mono_r; lia. }
rewrite u64_lit by lia. apply Z_to_le_bytes_of_bytes.
Qed.

Lemma word_to_le_bytes_of_bytes_n : forall n bs,
length bs = n -> (n <= 8)%nat ->
word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof. intros n bs <- Hn. apply word_to_le_bytes_of_bytes. exact Hn. Qed.

Section KnowTests.
Variable segs : list Segment.

Lemma adenot_SA : forall E b off, adenot E (SA b off) = Z_to_bv 64 (estart E (SA b off)).
Proof. intros. unfold adenot, v_addi, estart. reflexivity. Qed.

Lemma kwritable_sound : forall E M allkn k b off n,
know_ok segs E M allkn ->
know_ok segs E M k -> kwritable allkn k b off n = true -> 0 <= n ->
store_ok segs M (Z_to_bv 64 (estart E (SA b off))) (Z.to_nat n) = true
/\ 0 <= estart E (SA b off) /\ estart E (SA b off) + n <= 2 ^ 64.
Proof.
intros E M allkn k b off n Hall HK H Hn. induction k as [|K rest IH]; [discriminate|].
apply Forall_cons_iff in HK as [HKK Hrest].
destruct K; try exact (IH Hrest H).
lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
cbn [kwritable] in H.
cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
bv_unsigned (edenot E b) + off + n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) (Z.to_nat n) = true
/\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + n <= 2 ^ 64).
{ intros A B. split; [|lia].
replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
apply Hs; [lia|]. rewrite Z2Nat.id by lia. lia. }
lazymatch type of H with (if ?c0 then _ else _) = _ => destruct c0 eqn:Hc0 end.
- destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
destruct (xlo allkn wn) as [wl|] eqn:Hx; [|discriminate]. apply Z.leb_le in Hc0.
pose proof (xlo_sound segs E M allkn wn wl Hall Hx) as Hwl. unfold elenZ in *. apply CORE; lia.
- lazymatch type of H with (if ?c1 then _ else _) = _ => destruct c1 eqn:Hc1; [|exact (IH Hrest H)] end.
apply andb_prop in Hc1 as [Hnn Hxi]. apply andb_prop in Hnn as [Hn0 Hn1].
apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn1. unfold two64 in Hn1.
destruct (xinside_sound segs E M allkn b off (ELit n) wb wk wn Hall Hxi) as [I1 I2].
unfold elenZ in I2 at 1. cbn [edenot] in I2. rewrite u64_lit in I2 by lia.
unfold estart in I1, I2. cbn [a_base a_off] in I1, I2. apply CORE; lia.
Qed.

Lemma kwritable_x_sound : forall E M allkn k b off n,
know_ok segs E M allkn ->
know_ok segs E M k -> kwritable_x allkn k b off n = true ->
(forall m, Z.of_nat m <= elenZ E n ->
store_ok segs M (Z_to_bv 64 (estart E (SA b off))) m = true)
/\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
apply Forall_cons_iff in HK as [HKK Hrest].
destruct K; try exact (IH Hrest H).
lazymatch type of H with context [KWr ?wa ?wl :: rest] => destruct wa as [wb wk]; rename wl into wn end.
cbn [kwritable_x] in H.
assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kwritable_x allkn rest b off n) = true ->
(c1 || c2)%bool = true \/ kwritable_x allkn rest b off n = true)
by (intros [|] [|]; cbn; auto).
apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hs]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in Hs, F1, F2, F4 |- *. cbn [a_base a_off] in Hs, F1, F2, F4 |- *.
pose proof (u64_range (edenot E n)) as Hnr.
assert (CORE : bv_unsigned (edenot E wb) + wk <= bv_unsigned (edenot E b) + off ->
bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E wb) + wk + elenZ E wn ->
(forall m, Z.of_nat m <= elenZ E n -> store_ok segs M (Z_to_bv 64 (bv_unsigned (edenot E b) + off)) m = true)
/\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
{ intros A B. split; [|unfold elenZ in *; lia]. intros m Hm.
replace (bv_unsigned (edenot E b) + off) with (bv_unsigned (edenot E wb) + wk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E wb) + wk))) by lia.
apply Hs; lia. }
apply orb_prop in H as [H|H].
- destruct (expr_eqb b wb && Z.leb wk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst wb.
destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
destruct (xlo allkn wn) as [wl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn wn wl Hall Hxl).
apply CORE; unfold elenZ in *; lia.
- pose proof (xinside_sound segs E M allkn b off n wb wk wn Hall H) as [A B].
unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

Lemma kzero_x_sound : forall E M allkn k b off n,
know_ok segs E M allkn ->
know_ok segs E M k -> kzero_x allkn k b off n = true ->
(forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (estart E (SA b off) + i)) = Some (Z_to_bv 8 0))
/\ 0 <= estart E (SA b off) /\ estart E (SA b off) + elenZ E n <= 2 ^ 64.
Proof.
intros E M allkn k b off n Hall HK H. induction k as [|K rest IH]; [discriminate|].
apply Forall_cons_iff in HK as [HKK Hrest].
destruct K; try exact (IH Hrest H).
lazymatch type of H with context [KZero ?za ?zl :: rest] => destruct za as [zb zk]; rename zl into zn end.
cbn [kzero_x] in H.
assert (H2w : forall c1 c2 : bool, (if c1 then true else if c2 then true else kzero_x allkn rest b off n) = true ->
(c1 || c2)%bool = true \/ kzero_x allkn rest b off n = true)
by (intros [|] [|]; cbn; auto).
apply H2w in H. destruct H as [H|H]; [|exact (IH Hrest H)].
cbn [kentry_ok] in HKK. destruct HKK as [Hfl Hz]. pose proof Hfl as Hfl'. destruct Hfl' as (F1 & F2 & F3 & F4).
unfold estart in Hz, F1, F2, F4 |- *. cbn [a_base a_off] in Hz, F1, F2, F4 |- *.
pose proof (u64_range (edenot E n)) as Hnr.
assert (CORE : bv_unsigned (edenot E zb) + zk <= bv_unsigned (edenot E b) + off ->
bv_unsigned (edenot E b) + off + elenZ E n <= bv_unsigned (edenot E zb) + zk + elenZ E zn ->
(forall i, 0 <= i < elenZ E n -> M (Z_to_bv 64 (bv_unsigned (edenot E b) + off + i)) = Some (Z_to_bv 8 0))
/\ 0 <= bv_unsigned (edenot E b) + off /\ bv_unsigned (edenot E b) + off + elenZ E n <= 2 ^ 64).
{ intros A B. split; [|unfold elenZ in *; lia]. intros i Hi.
replace (bv_unsigned (edenot E b) + off + i) with (bv_unsigned (edenot E zb) + zk + (bv_unsigned (edenot E b) + off - (bv_unsigned (edenot E zb) + zk) + i)) by lia.
apply Hz. lia. }
apply orb_prop in H as [H|H].
- destruct (expr_eqb b zb && Z.leb zk off)%bool eqn:H01; [|discriminate]. apply andb_prop in H01 as [H0 H1].
apply expr_eqb_eq in H0. apply Z.leb_le in H1. subst zb.
destruct (xhi allkn n) as [nh|] eqn:Hxh; [|discriminate].
destruct (xlo allkn zn) as [zl|] eqn:Hxl; [|discriminate]. apply Z.leb_le in H.
pose proof (xhi_sound segs E M allkn n nh Hall Hxh). pose proof (xlo_sound segs E M allkn zn zl Hall Hxl).
apply CORE; unfold elenZ in *; lia.
- pose proof (xinside_sound segs E M allkn b off n zb zk zn Hall H) as [A B].
unfold estart in A, B. cbn [a_base a_off] in A, B. apply CORE; lia.
Qed.

Lemma kimg_cut_sound : forall E M k a n,
know_ok segs E M k -> know_ok segs E M (kimg_cut k a n).
Proof.
intros E M k a n HK. unfold kimg_cut, know_ok. apply Forall_flat_map. apply Forall_forall. intros K Hin.
pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
unfold kimg_cut1. destruct K; try (apply Forall_one; exact HKK).
lazymatch goal with |- context [KImg ?l ?h] => rename l into lo; rename h into hi end.
destruct (Z.leb hi a || Z.leb (a + n) lo)%bool eqn:Hc; [apply Forall_one; exact HKK|].
apply orb_false_iff in Hc as [Hc1 Hc2]. apply Z.leb_gt in Hc1. apply Z.leb_gt in Hc2.
cbn [kentry_ok] in HKK. destruct HKK as (H0 & Hhi & Hnone).
apply Forall_app. split.
- destruct (Z.ltb lo a) eqn:Hl; [|constructor]. apply Z.ltb_lt in Hl. apply Forall_one. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
- destruct (Z.ltb (a + n) hi) eqn:Hh; [|constructor]. apply Z.ltb_lt in Hh. apply Forall_one. cbn [kentry_ok].
split; [lia|]. split; [lia|]. intros i Hi. apply Hnone. lia.
Qed.

Definition piece_ok (E : env) (M : word -> option byte) (b : expr) (off : Z) (w : nat) (v : expr) : Prop :=
exists bs, rdn segs M (Z_to_bv 64 (estart E (SA b off))) w = Some bs /\ length bs = w
/\ word_to_le_bytes w (edenot E v) = bs.

Lemma lookup_piece : forall E M k b off w v hs,
know_ok segs E M k -> (1 <= w <= 8)%nat ->
know_lookup segs k b off w false [] [] = LHit v [] hs ->
flat E (SA b off) (Z.of_nat w) ->
piece_ok E M b off w v.
Proof.
intros E M k b off w v hs HK Hw HL Hfl.
pose proof (know_lookup_sound segs E M k b off w false [] [] HK ltac:(lia) ltac:(lia)) as X.
rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
exists bs. rewrite <- adenot_SA. split; [exact Hrd|]. split; [exact Hlen|].
unfold extz in Hv. rewrite <- Hv, <- Hlen. apply word_to_le_bytes_of_bytes. lia.
Qed.

Lemma kread8e_piece : forall E M k b off v,
know_ok segs E M k -> kread8e segs k b off = Some v -> flat E (SA b off) 8 ->
piece_ok E M b off 8 v.
Proof.
intros E M k b off v HK H Hfl. unfold kread8e in H.
destruct (know_lookup segs k b off 8 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
destruct scs; [|discriminate]. injection H as ->.
eapply lookup_piece; [exact HK | lia | exact HL | exact Hfl].
Qed.

Lemma kreadZ1_byte : forall E M k b off z,
know_ok segs E M k -> kreadZ segs k b off 1 = Some z -> flat E (SA b off) 1 ->
rdn segs M (Z_to_bv 64 (estart E (SA b off))) 1 = Some [Z_to_bv 8 z] /\ 0 <= z < 256.
Proof.
intros E M k b off z HK H Hfl. unfold kreadZ in H.
destruct (know_lookup segs k b off 1 false [] []) as [v' scs hs|scs hs|] eqn:HL; try discriminate.
destruct v' as [z0| | | | | | |]; try discriminate. destruct scs; [|discriminate]. injection H as <-.
pose proof (know_lookup_sound segs E M k b off 1 false [] [] HK ltac:(lia) ltac:(lia)) as X.
rewrite HL in X. destruct (X ltac:(constructor) Hfl) as (bs & Hrd & Hlen & Hv).
destruct bs as [|b0 [|]]; try discriminate.
cbn [edenot] in Hv. unfold extz in Hv. rewrite bytes_le_single in Hv.
apply (f_equal bv_unsigned) in Hv. rewrite !u_lit64 in Hv.
pose proof (bv_unsigned_in_range _ b0) as Hr. change (bv_modulus 8) with 256 in Hr.
rewrite (Z.mod_small (bv_unsigned b0)) in Hv by (unfold two64; lia).
split; [|rewrite <- Hv; lia]. rewrite <- adenot_SA, Hrd. f_equal. f_equal. apply bv_eq.
rewrite Z_to_bv_unsigned, <- Hv. symmetry. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma kread_bytes_sound : forall E M k len b off zs,
know_ok segs E M k -> kread_bytes segs len k b off = Some zs ->
0 <= estart E (SA b off) -> estart E (SA b off) + Z.of_nat len <= 2 ^ 64 ->
rdn segs M (Z_to_bv 64 (estart E (SA b off))) len = Some (map (fun z => Z_to_bv 8 z) zs)
/\ length zs = len /\ Forall (fun z => 0 <= z < 256) zs.
Proof.
intros E M k len. induction len as [|len IH]; intros b off zs HK H Hlo Hhi.
- cbn in H. injection H as <-. split; [reflexivity|]. split; [reflexivity | constructor].
- cbn [kread_bytes] in H.
destruct (kreadZ segs k b off 1) as [z|] eqn:Hz; [|discriminate].
destruct (kread_bytes segs len k b (off + 1)) as [rest|] eqn:Hrest; [|discriminate].
injection H as <-.
assert (Hfl : flat E (SA b off) 1) by (unfold flat; lia).
destruct (kreadZ1_byte E M k b off z HK Hz Hfl) as [Hrd Hzr].
destruct (IH b (off + 1) rest HK Hrest ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)
ltac:(unfold estart in *; cbn [a_base a_off] in *; lia)) as (Hrd2 & Hlen & Hall).
split; [| split; [cbn; lia | constructor; assumption]].
change (S len) with (1 + len)%nat. cbn [map].
change (Z_to_bv 8 z :: map (fun z0 : Z => Z_to_bv 8 z0) rest) with ([Z_to_bv 8 z] ++ map (fun z0 : Z => Z_to_bv 8 z0) rest).
eapply rdn_app; [exact Hrd|].
replace (Z_to_bv 64 (estart E (SA b off)) + nat_to_word 1)%bv with (Z_to_bv 64 (estart E (SA b (off + 1)))); [exact Hrd2|].
apply bv_eq. unfold nat_to_word, estart. cbn [a_base a_off]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
change (Z.of_nat 1) with 1. rewrite (Z.mod_small 1) by lia.
rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.

Lemma zbytes_of_small : forall zs, Forall (fun z => 0 <= z < 256) zs ->
zbytes_le_to_Z zs = bytes_le_to_Z (map (fun z => Z_to_bv 8 z) zs).
Proof.
intros zs Hall. rewrite <- zbytes_map. rewrite map_map. f_equal.
induction Hall as [|z rest Hz Hrest IH]; [reflexivity|]. cbn [map]. f_equal; [|exact IH].
symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256. lia.
Qed.

Lemma copy_facts_sound : forall E M k sb db fuel sk dk n kc,
know_ok segs E M k ->
copy_facts segs fuel k sb sk db dk n = Some kc -> 0 <= n -> (Z.to_nat n <= fuel)%nat ->
0 <= estart E (SA sb sk) -> estart E (SA sb sk) + n <= 2 ^ 64 ->
0 <= estart E (SA db dk) -> estart E (SA db dk) + n <= 2 ^ 64 ->
exists bs, length bs = Z.to_nat n
/\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
/\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc.
Proof.
intros E M k sb db fuel. induction fuel as [|f IH]; intros sk dk n kc HK H Hn Hfuel Slo Shi Dlo Dhi.
- cbn [copy_facts] in H. injection H as <-. assert (n = 0) by lia. subst n.
exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
- cbn [copy_facts] in H.

assert (STEP : forall (w : nat) v kr,
(1 <= w <= 8)%nat -> Z.of_nat w <= n ->
piece_ok E M sb sk w v ->
copy_facts segs f k sb (sk + Z.of_nat w) db (dk + Z.of_nat w) (n - Z.of_nat w) = Some kr ->
kc = KWord (SA db dk) w v :: kr ->
exists bs, length bs = Z.to_nat n
/\ rdn segs M (Z_to_bv 64 (estart E (SA sb sk))) (Z.to_nat n) = Some bs
/\ forall M', rdn segs M' (Z_to_bv 64 (estart E (SA db dk))) (Z.to_nat n) = Some bs -> know_ok segs E M' kc).
{ intros w v kr Hw Hwn (bsP & HrdP & HlenP & HvP) Hr ->.
assert (ES : estart E (SA sb (sk + Z.of_nat w)) = estart E (SA sb sk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
assert (ED : estart E (SA db (dk + Z.of_nat w)) = estart E (SA db dk) + Z.of_nat w) by (unfold estart; cbn [a_base a_off]; lia).
destruct (IH (sk + Z.of_nat w) (dk + Z.of_nat w) (n - Z.of_nat w) kr HK Hr ltac:(lia) ltac:(lia)
ltac:(rewrite ES; lia) ltac:(rewrite ES; lia) ltac:(rewrite ED; lia) ltac:(rewrite ED; lia))
as (bsR & HlenR & HrdR & HKR).
exists (bsP ++ bsR). split; [rewrite length_app; lia|]. split.
- replace (Z.to_nat n) with (w + Z.to_nat (n - Z.of_nat w))%nat by lia.
apply rdn_app; [rewrite <- HlenP at 1; rewrite HlenP; exact HrdP|].
rewrite ES in HrdR.
replace (Z_to_bv 64 (estart E (SA sb sk)) + nat_to_word w)%bv with (Z_to_bv 64 (estart E (SA sb sk) + Z.of_nat w)); [exact HrdR|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity.
- intros M' HM'. constructor.
+ cbn [kentry_ok]. split; [lia|]. split; [unfold flat; lia|].
rewrite adenot_SA, HvP.
pose proof (rdn_firstn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as F.
rewrite F. f_equal. rewrite firstn_app, HlenP, Nat.sub_diag. cbn [firstn]. rewrite firstn_all2 by lia. apply app_nil_r.
+ apply HKR. rewrite ED.
pose proof (rdn_skipn segs M' (Z.to_nat n) _ _ w HM' ltac:(lia)) as Sk.
replace (Z.to_nat (n - Z.of_nat w)) with (Z.to_nat n - w)%nat by lia.
replace (Z_to_bv 64 (estart E (SA db dk) + Z.of_nat w)) with (Z_to_bv 64 (estart E (SA db dk)) + nat_to_word w)%bv.
2:{ apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
rewrite (Z.mod_small (Z.of_nat w)) by lia. rewrite Z.add_mod_idemp_l by lia. reflexivity. }
rewrite Sk. f_equal. rewrite skipn_app, HlenP, Nat.sub_diag. cbn [skipn]. rewrite skipn_all2 by lia. reflexivity. }
match type of H with (if ?c then _ else _) = _ => destruct c eqn:H8 end.
+ apply andb_prop in H8 as [H8 Hknown]. apply Z.leb_le in H8.
destruct (copy_facts segs f k sb (sk + 8) db (dk + 8) (n - 8)) as [kr|] eqn:Hr;
[|destruct (kread8e segs k sb sk); [discriminate|]; destruct (kread_bytes segs 8 k sb sk); discriminate].
assert (Hfl8 : flat E (SA sb sk) 8) by (unfold flat; lia).
destruct (kread8e segs k sb sk) as [v|] eqn:Hv.
* injection H as <-. apply (STEP 8%nat v kr); [lia | lia | | exact Hr | reflexivity].
eapply kread8e_piece; [exact HK | exact Hv | exact Hfl8].
* destruct (kread_bytes segs 8 k sb sk) as [zs|] eqn:Hzs; [|discriminate]. injection H as <-.
apply (STEP 8%nat (ELit (zbytes_le_to_Z zs)) kr); [lia | lia | | exact Hr | reflexivity].
destruct (kread_bytes_sound E M k 8 sb sk zs HK Hzs ltac:(lia) ltac:(lia)) as (Hrd & Hlen & Hsmall).
exists (map (fun z => Z_to_bv 8 z) zs). split; [exact Hrd|]. split; [rewrite length_map; exact Hlen|].
cbn [edenot]. rewrite (zbytes_of_small zs Hsmall).
replace 8%nat with (length (map (fun z : Z => Z_to_bv 8 z) zs)) at 1 by (rewrite length_map; exact Hlen).
apply word_to_le_bytes_of_bytes. rewrite length_map. lia.
+ clear H8. destruct (Z.leb 1 n) eqn:H1.
* apply Z.leb_le in H1.
destruct (know_lookup segs k sb sk 1 false [] []) as [v scs hs|scs hs|] eqn:HL; try discriminate.
destruct scs; [|discriminate].
destruct (copy_facts segs f k sb (sk + 1) db (dk + 1) (n - 1)) as [kr|] eqn:Hr; [|discriminate].
injection H as <-. apply (STEP 1%nat v kr); [lia | lia | | exact Hr | reflexivity].
eapply lookup_piece; [exact HK | lia | exact HL | unfold flat; lia].
* injection H as <-. apply Z.leb_gt in H1. assert (n = 0) by lia. subst n.
exists []. split; [reflexivity|]. split; [reflexivity|]. intros M' _. constructor.
Qed.

End KnowTests.

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.

Definition res_len_okP : Prop := length (segments_reserved SEGS) = n_res A.
Definition hull_okP : Prop := 0 <= img_lo A /\ img_lo A mod 4096 = 0 /\ img_hi A mod 4096 = 0 /\ img_hi A <= KHI.
Hypothesis RES_len : res_len_okP.
Hypothesis HULL_ok : hull_okP.
Variable USP : Z.
Hypothesis NX0_ge : APS.nx0_ge nx0.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

Variable FS0 : Fs.Fs.

Definition segs_wr_ok : Prop := forall seg, In seg SEGS -> seg_writable seg = true -> seg_readable seg = true.
Hypothesis SEGS_wr : segs_wr_ok.

#[local] Notation cfg := (cfg_of SEGS) (only parsing).
#[local] Notation CSOK := (cs_ok SEGS A LIMIT USP SINV argH FS0) (only parsing).
#[local] Notation HID := (hid A USP argH) (only parsing).
#[local] Notation MR := (Mr A USP argH) (only parsing).

#[local] Ltac aps_fill :=
first [eassumption | exact (fun _ : nat => @None acs) | exact (fun _ _ _ => None) | exact (fun _ _ => None) | exact (fun _ => None)
| exact 0%nat | exact 0%Z | exact nx0 | exact LIMIT | exact USP].

Lemma w_reg_sound : forall E cs R FULL model n,
CSOK E cs R FULL model -> (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (reg cs n).
Proof. intros. eapply reg_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_reg_lit_sound : forall E cs R FULL model n z,
CSOK E cs R FULL model -> (0 < n < 32)%nat -> reg_lit cs n = Some z ->
getr R (Z_to_bv 5 (Z.of_nat n)) = Z_to_bv 64 z /\ 0 <= z < two64.
Proof. intros. eapply reg_lit_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_split_lit_denot : forall E e b k, split_lit e = (b, k) ->
edenot E e = Z_to_bv 64 (bv_unsigned (edenot E b) + k).
Proof. intros. eapply split_lit_denot; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_know_ok_havoc : forall E M M' k b o n,
know_ok SEGS E M k ->
(forall x : word, bv_unsigned x < estart E (SA b o) \/ estart E (SA b o) + elenZ E n <= bv_unsigned x -> M' x = M x) ->
mem_grows M M' ->
know_ok SEGS E M' (kn_havoc k b o n).
Proof. intros. eapply know_ok_havoc; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_flat_x_sound : forall E M k b off n,
know_ok SEGS E M k -> flat_x k b off n = true ->
0 <= estart E (SA b off) /\ estart E (SA b off) + bv_unsigned (edenot E n) <= 2 ^ 64 /\ 0 < bv_unsigned (edenot E n).
Proof. intros. eapply flat_x_sound; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_env_agree_le : forall b b' E E', env_agree b' E E' -> (b <= b')%nat -> env_agree b E E'.
Proof. intros b b' E E' [Hv Hb] Hle. split; [|exact Hb]. intros n Hn. apply Hv. lia. Qed.

Lemma w_cs_ok_agree : forall E E' cs R FULL model,
env_agree (nxt cs) E E' -> fresh_ok nx0 cs = true -> CSOK E cs R FULL model -> CSOK E' cs R FULL model.
Proof. intros. eapply cs_ok_agree; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_hid_agree : forall b E E' cs model,
env_agree b E E' -> (nx0 <= b)%nat -> pairs_vars_lt b (a_vis cs ++ a_ghost cs) = true ->
HID E' cs model = HID E cs model.
Proof. intros. eapply hid_agree; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_cs_ok_frame : forall E cs R FULL model ss' R' FULL' model',
CSOK E cs R FULL model -> same_but_materialized model model' -> MInv (allowA A E cs) model' ->
regs_ok E (s_regs ss') R' -> s_log ss' = [] ->
know_ok SEGS E (MR E cs model FULL') (s_know ss') ->
(forall a, HID E cs model a = true -> FULL' a = FULL a) ->
CSOK E (with_ss cs ss') R' FULL' model'.
Proof. intros. eapply cs_ok_frame; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_lazy_cover_cs : forall E cs R FULL model,
CSOK E cs R FULL model -> lazy_cover (HID E cs model) (m_vm_lazy model) (allowA A E cs).
Proof. intros. eapply lazy_cover_cs; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_A_wf_allowA : forall E cs, A_wf (allowA A E cs).
Proof. intros. eapply A_wf_allowA; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_H_off_segments_cs : forall E cs model, H_off_segments SEGS (HID E cs model).
Proof. intros. eapply H_off_segments_cs; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma w_fresh_ok_parts : forall cs, fresh_ok nx0 cs = true ->
AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true /\ AP.kn_vars_lt (nxt cs) (kn cs) = true
/\ maps_vars_lt (nxt cs) (a_maps cs) = true /\ pairs_vars_lt (nxt cs) (a_vis cs ++ a_ghost cs) = true
/\ AP.expr_vars_lt (nxt cs) (a_brk cs) = true /\ fd_vars_lt (nxt cs) (a_fd cs) = true /\ (nx0 <= nxt cs)%nat.
Proof. intros. eapply fresh_ok_parts; try eassumption. Unshelve. all: aps_fill. Qed.

Lemma find_segment_In : forall segs a n seg, find_segment segs a n = Some seg -> In seg segs.
Proof.
intros segs a n seg. induction segs as [|s0 rest IH]; cbn [find_segment]; intros H; [discriminate|].
destruct (Z.leb (Z.of_N (seg_base s0)) a && Z.leb (a + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
- injection H as <-. left. reflexivity.
- right. apply IH. exact H.
Qed.

Lemma wview_rd1 : forall M (a : word) b,
wview SEGS M a = Some b ->
(match M a with Some b0 => Some b0 | None => seg_rom SEGS a end) = Some b.
Proof.
intros M a b H. unfold wview in H. destruct (M a) as [b0|]; [exact H|].
unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
destruct (find_segment SEGS (bv_unsigned a) 1) as [seg|] eqn:Hf; [|discriminate].
destruct (seg_writable seg) eqn:Hw; [|discriminate].
rewrite (SEGS_wr seg (find_segment_In _ _ _ _ Hf) Hw).
change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes]. rewrite H. reflexivity.
Qed.

Lemma store_ok_rdn : forall n M (a : word),
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
store_ok SEGS M a n = true ->
exists bs, rdn SEGS M a n = Some bs /\ length bs = n.
Proof.
induction n as [|n IH]; intros M a Hnw Hst.
- exists []. split; reflexivity.
- cbn [store_ok] in Hst. destruct (wview SEGS M a) as [b|] eqn:Hv; [|discriminate].
cbn [rdn]. rewrite (wview_rd1 M a b Hv).
destruct n as [|n'].
+ exists [b]. split; reflexivity.
+ assert (Hu1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
destruct (IH M (a + 1)%bv ltac:(rewrite Hu1; lia) Hst) as (bs & Hrd & Hlen).
rewrite Hrd. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

Lemma call_core : forall cs E E' R FULL model T (ret : Z) sr2 k' nx2 regs' MR',
CSOK E cs R FULL model ->
fresh_ok nx0 cs = true ->
env_agree (nxt cs) E E' ->
msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
regs_ok E' sr2 regs' ->
know_ok SEGS E' MR' k' ->
(forall R' FULL' model',
CSOK E' (with_ss cs (mk_ss ret sr2 k' nx2)) R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' ret FULL' model') T) ->
srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
intros cs E E' R FULL model T ret sr2 k' nx2 regs' MR' HC Hfresh Hag Hms HR' HK' Hk.
destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (H := HID E cs model).
unfold cfg_of.
apply (srz_msteps_restricted_T SEGS H
(w_H_off_segments_cs E cs model) SEGS_wx (allowA A E cs)
(mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS)) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) model T
(w_lazy_cover_cs E cs R FULL model HC)
(w_A_wf_allowA E cs)
(co_minv _ _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ _ HC)).
- rewrite restrict_mkst. exact Hms.
- intros model' Hinv' Hsame Hclean.
set (FULL' := munrestrict H FULL MR').
change (unrestrict H (ms_mem (mkst R (Z_to_bv 64 (pc cs)) FULL (seg_rom SEGS))) (mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)))
with (mkst regs' (Z_to_bv 64 ret) FULL' (seg_rom SEGS)).
apply (Hk regs' FULL' model').
+ pose proof (w_cs_ok_agree E E' cs R FULL model Hag Hfresh HC) as HC1.
pose proof (w_hid_agree (nxt cs) E E' cs model Hag Fle Fallow) as HH.
eapply (w_cs_ok_frame E' cs R FULL model _ regs' FULL' model' HC1 Hsame).
* rewrite (allowA_agree A (nxt cs) E E' cs Hag Fallow). exact Hinv'.
* exact HR'.
* reflexivity.
* cbn [s_know mk_ss]. unfold Mr. rewrite HH.
fold H. unfold FULL'. rewrite (mrestrict_munrestrict_clean H FULL MR') by (intros a Ha; exact (Hclean a Ha)).
exact HK'.
* intros a Ha. rewrite HH in Ha.
unfold FULL', munrestrict. fold H in Ha. rewrite Ha. reflexivity.
+ apply (same_but_materialized_frame _ _ Hsame).
Qed.

Lemma sr_vars_lt_fresh : forall rs sr nx b,
AP.sr_vars_lt b sr = true -> (nx + length rs <= b)%nat -> AP.sr_vars_lt b (sr_fresh sr rs nx) = true.
Proof.
induction rs as [|r rest IH]; intros sr nx b Hsr Hb; cbn [sr_fresh length] in *; [exact Hsr|].
apply IH; [|lia]. apply sr_vars_lt_upd; [exact Hsr|]. cbn [AP.expr_vars_lt]. apply Nat.ltb_lt. lia.
Qed.

Lemma call_node_sound : forall cs cs' E R FULL model T (ret : Z) rv k' regs' MR',
CSOK E cs R FULL model ->
after_call nx0 cs ret rv k' = Some cs' ->
msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
kept_ok R regs' ->
match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
know_ok SEGS E MR' k' ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
intros cs cs' E R FULL model T ret rv k' regs' MR' HC Hac Hms Hkept Hrv HK' Hk.
unfold after_call in Hac.
match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
injection Hac as <-.
destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (E' := ext_call E (nxt cs) regs').
pose proof (ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
eapply (call_core cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms).
- apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I].
- eapply know_ok_agree'; [exact Hag | exact Hkv | exact HK'].
- intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

Definition ext_call2 (E : env) (nx : nat) (R' : bvmap 5 word) (vals : list word) : env :=
ext_list (ext_call E nx R') (nx + NCS) vals.

Lemma ext_call2_agree : forall E nx R' vals, env_agree nx E (ext_call2 E nx R' vals).
Proof.
intros E nx R' vals. unfold ext_call2.
destruct (ext_call_agree E nx R') as [H1 H2]. destruct (ext_list_agree (ext_call E nx R') (nx + NCS) vals) as [H3 H4].
split; [|rewrite H2; exact H4]. intros n Hn. rewrite H1 by exact Hn. apply H3. lia.
Qed.

Lemma ext_call2_agree16 : forall E nx R' vals, env_agree (nx + NCS) (ext_call E nx R') (ext_call2 E nx R' vals).
Proof. intros. unfold ext_call2. apply ext_list_agree. Qed.

Lemma ext_call2_at : forall E nx R' vals i, (i < length vals)%nat ->
ev (ext_call2 E nx R' vals) (nx + NCS + i) = nth i vals (Z_to_bv 64 0).
Proof. intros. unfold ext_call2. apply ext_list_at. assumption. Qed.

Lemma call_node_sound2 : forall cs cs' E R FULL model T (ret : Z) rv k' extra vals regs' MR',
CSOK E cs R FULL model ->
after_call2 nx0 cs ret rv k' extra = Some cs' ->
msteps SEGS (mkst R (Z_to_bv 64 (pc cs)) (MR E cs model FULL) (seg_rom SEGS))
(mkst regs' (Z_to_bv 64 ret) MR' (seg_rom SEGS)) ->
kept_ok R regs' ->
match rv with Some e => getr regs' (Z_to_bv 5 10) = edenot E e | None => True end ->
know_ok SEGS (ext_call2 E (nxt cs) regs' vals) MR' k' ->
(forall E' R' FULL' model',
env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> CSOK E' cs' R' FULL' model' -> m_fs model' = m_fs model ->
srealizes SEGS (cfg R' (pc cs') FULL' model') T) ->
srealizes SEGS (cfg R (pc cs) FULL model) T.
Proof.
intros cs cs' E R FULL model T ret rv k' extra vals regs' MR' HC Hac Hms Hkept Hrv HK' Hk.
unfold after_call2 in Hac.
match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hc; [|discriminate] end.
apply andb_prop in Hc as [Hc Hrvv]. apply andb_prop in Hc as [Hfresh Hkv].
injection Hac as <-.
destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
set (E' := ext_call2 E (nxt cs) regs' vals).
pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag. fold E' in Hag.
set (sr1 := sr_fresh (s_regs (a_ss cs)) caller_saved (nxt cs)).
assert (Hsf : AP.sr_vars_lt (nxt cs + NCS) sr1 = true).
{ subst sr1. apply sr_vars_lt_fresh; [eapply sr_vars_lt_mono; [exact Fsr | lia] | ].
unfold caller_saved, NCS. cbn [length]. lia. }
assert (HR2 : regs_ok E' (match rv with Some e => sr_upd sr1 10 e | None => sr1 end) regs').
{ eapply (regs_ok_agree' (nxt cs + NCS)); [apply ext_call2_agree16 | |].
- destruct rv as [e|]; [|exact Hsf]. apply sr_vars_lt_upd; [exact Hsf|]. eapply expr_vars_lt_mono; [exact Hrvv | unfold nxt, NCS; lia].
- subst sr1. apply (regs_after_call E _ R regs' (nxt cs) rv (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC) Fsr Hkept).
destruct rv as [e|]; [split; [exact Hrvv | exact Hrv] | exact I]. }
eapply (call_core cs E E' R FULL model T ret _ k' _ regs' MR' HC Hfresh Hag Hms HR2 HK').
intros R' FULL' model' HC' Hfs. apply (Hk E' R' FULL' model'); [| exact HC' | exact Hfs].
split; [eapply w_env_agree_le; [exact Hag | exact Fle] | exact Hag].
Qed.

Lemma ret_lit_sound : forall E cs R FULL model r,
CSOK E cs R FULL model -> ret_lit cs = Some r ->
getr R (Z_to_bv 5 1) = Z_to_bv 64 r /\ ret_ok (Z_to_bv 64 r) /\ 0 <= r < two64.
Proof.
intros E cs R FULL model r HC H. unfold ret_lit in H.
destruct (reg cs 1) as [z| | | | | | |] eqn:Hr; try discriminate.
destruct (Z.eqb (z mod 2) 0 && Z.ltb z two64 && Z.leb 0 z)%bool eqn:Hc; [|discriminate]. injection H as <-.
apply andb_prop in Hc as [Hc H0]. apply andb_prop in Hc as [He Hlt].
apply Z.eqb_eq in He. apply Z.ltb_lt in Hlt. apply Z.leb_le in H0.
pose proof (w_reg_sound E cs R FULL model 1 HC ltac:(lia)) as R1.
rewrite Hr in R1. cbn [edenot] in R1.
split; [exact R1|]. split; [| lia]. apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hlt; lia). exact He.
Qed.

Lemma split_lit_vars : forall e b k m, split_lit e = (b, k) -> AP.expr_vars_lt m e = true -> AP.expr_vars_lt m b = true.
Proof.
intros e b k m H Hv. unfold split_lit in H.
destruct e; try (injection H as <- <-; first [exact Hv | reflexivity]).
lazymatch type of H with (match ?o with _ => _ end) = _ => destruct o end; try (injection H as <- <-; exact Hv).
lazymatch type of H with (match ?y with _ => _ end) = _ => destruct y end; try (injection H as <- <-; exact Hv).
injection H as <- <-. cbn [AP.expr_vars_lt] in Hv. apply andb_prop in Hv as [Hv _]. exact Hv.
Qed.

Lemma nth_map_seq : forall {T} (f : nat -> T) W i d, (i < W)%nat -> nth i (map f (seq 0 W)) d = f i.
Proof.
intros T f W i d Hi. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact Hi).
rewrite map_nth. rewrite seq_nth by exact Hi. reflexivity.
Qed.

Lemma nth_repeat_lt : forall {T} (a d : T) m j, (j < m)%nat -> nth j (repeat a m) d = a.
Proof. intros T a d m. induction m as [|m IH]; intros j Hj; [lia|]. destruct j; [reflexivity|]. cbn. apply IH. lia. Qed.

Lemma k0_sound : forall E M k db dk ne dst k0,
know_ok SEGS E M k ->
(if off_image_x A k db dk ne then Some k
else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) = Some k0 ->
know_ok SEGS E M k0.
Proof.
intros E M k db dk ne dst k0 HK H.
destruct (off_image_x A k db dk ne); [injection H as <-; exact HK|].
destruct dst; try discriminate. destruct ne; try discriminate. injection H as <-.
apply kimg_cut_sound. exact HK.
Qed.

Lemma wbytes_fill_at : forall M (s : word) b n i,
bv_unsigned s + n <= 2 ^ 64 -> 0 <= i < n ->
wbytes M s (repeat b (Z.to_nat n)) (Z_to_bv 64 (bv_unsigned s + i)) = Some b.
Proof.
intros M s b n i Hnw Hi.
replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite wbytes_nth by (rewrite repeat_length; lia). f_equal. apply nth_repeat_lt. lia.
Qed.

Lemma Z_to_bv8_mod : forall c, Z_to_bv 8 (c mod 256) = Z_to_bv 8 c.
Proof.
intros c. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
apply Z.mod_mod. lia.
Qed.

Lemma summary_fill_sound : forall entry cmax,
fill_spec SEGS entry cmax ->
node1_stmt SEGS A nx0 LIMIT USP SINV argH FS0 always (fun cs => summary_fill A nx0 cs entry cmax).
Proof.
intros entry cmax SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
rewrite summary_fill_eq in Hn.  unfold summary_fill_ref in Hn.
destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
destruct (reg_lit cs 11) as [c|] eqn:H11; [|discriminate].
destruct (Z.ltb c cmax) eqn:Hcm; [|discriminate]. cbn [negb] in Hn. apply Z.ltb_lt in Hcm.
destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate].
destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate].
destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
apply andb_prop in Hcond as [Hcond Hb]. apply andb_prop in Hcond as [Hn0 Hn40].
apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb. unfold two64 in Hb.

destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
destruct (w_reg_lit_sound E cs R FULL model 11 c HC ltac:(lia) H11) as [R11 Hc].
pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo'.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi'.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
set (s := edenot E (reg cs 10)) in *. set (nw := edenot E (reg cs 12)) in *. set (n := bv_unsigned nw) in *.
pose proof (u64_range nw) as Hnr. fold n in Hnr.
assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
assert (Hlen : elenZ E (reg cs 12) = n) by reflexivity.

assert (FIN : forall k',
store_ok SEGS M s (Z.to_nat n) = true ->
know_ok SEGS E (wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))) k' ->
after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
srealizes SEGS (cfg R (pc cs) FULL model) T).
{ intros k' Hst HK' Hac.
destruct (SUM M s (Z_to_bv 64 c) n R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) Hst
ltac:(rewrite u64_lit by (unfold two64 in Hc; lia); lia) Hrok R1 R10 R11 ltac:(rewrite Hnwn; exact R12))
as (regs' & Hms & Hkept & Ha0).
rewrite (u64_lit c) in Hms by (unfold two64 in Hc; lia).
eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
- rewrite Hpc. exact Hms.
- exact Hkept.
- exact Ha0.
- exact HK'.
- exact Hk. }
assert (ST0 : n = 0 -> store_ok SEGS M s (Z.to_nat n) = true) by (intros ->; reflexivity).
assert (WB0 : n = 0 -> wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n)) = M) by (intros ->; reflexivity).

destruct (Z.eqb nhi 0) eqn:Hnhi0.
{ apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
apply (FIN (kn cs)); [exact (ST0 Hz) | rewrite (WB0 Hz); exact HKN | exact Hn]. }

match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzb end.
{ apply andb_prop in Hzb as [Hzb Hwr]. apply andb_prop in Hzb as [Hc8 Hkz]. apply Z.eqb_eq in Hc8.
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hkz) as (Zb & _ & _).
rewrite Hse, Hlen in *.
apply (FIN (kn cs)); [apply Wst; lia | | exact Hn].
destruct (Z.eq_dec n 0) as [Hz|Hnz]; [rewrite (WB0 Hz); exact HKN|].
assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
rewrite wbytes_same; [exact HKN | rewrite repeat_length; lia |].
intros j Hj. rewrite repeat_length in Hj. rewrite nth_repeat_lt by exact Hj.
rewrite Hus. rewrite Zb by lia. rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity. }
clear Hzb.

match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
pose proof (k0_sound E M (kn cs) db dk (reg cs 12) (reg cs 10) k0 HKN Hk0) as HK0.
destruct (kwritable_x (kn cs) (kn cs) db dk (reg cs 12)) eqn:Hwr; [|discriminate].
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (reg cs 12) HKN HKN Hwr) as (Wst & Wlo & Whi).
rewrite Hse, Hlen in *.
eapply FIN; [apply Wst; lia | | exact Hn].
set (M' := wbytes M s (repeat (Z_to_bv 8 c) (Z.to_nat n))).
assert (HK1 : know_ok SEGS E M' (kn_havoc k0 db dk (reg cs 12))).
{ eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
intros x Hx. rewrite Hlen in Hx. destruct (Z.eq_dec n 0) as [Hz|Hnz]; [subst M'; rewrite (WB0 Hz); reflexivity|].
assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
subst M'. apply wbytes_out; rewrite repeat_length; lia. }
destruct (Z.ltb 0 nlo) eqn:Hpos; [|exact HK1]. apply Z.ltb_lt in Hpos.
assert (Hus : bv_unsigned s = estart E (SA db dk)) by (rewrite <- Hse; apply u64_lit; lia).
assert (FILL : forall i, 0 <= i < n -> M' (Z_to_bv 64 (estart E (SA db dk) + i)) = Some (Z_to_bv 8 c)).
{ intros i Hi. subst M'. rewrite <- Hus. apply wbytes_fill_at; lia. }
constructor; [|exact HK1].
destruct (Z.eqb (c mod 256) 0) eqn:Hc8; cbn [kentry_ok]; rewrite Hlen.
- apply Z.eqb_eq in Hc8. split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite <- (Z_to_bv8_mod c), Hc8. reflexivity.
- split; [unfold flat; lia|]. intros i Hi. rewrite (FILL i Hi). rewrite Z_to_bv8_mod. reflexivity.
Qed.

Lemma store_ok_sub : forall M (a : word) n (b : word) m,
bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
store_ok SEGS M a n = true ->
bv_unsigned a <= bv_unsigned b -> bv_unsigned b + Z.of_nat m <= bv_unsigned a + Z.of_nat n ->
store_ok SEGS M b m = true.
Proof.
intros M a n b m Hnw Hst Hlo Hhi. apply store_ok_of_all; [lia|].
intros x Hx. eapply (store_ok_all SEGS M n a Hnw Hst). lia.
Qed.

Lemma summary_miz_sound :
miz_spec SEGS (x_memiszero A) ->
node1_stmt SEGS A nx0 LIMIT USP SINV argH FS0 always (fun cs => summary_miz A nx0 cs).
Proof.
intros SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
rewrite summary_miz_eq in Hn.  unfold summary_miz_ref in Hn.
destruct (Z.eqb (pc cs) (x_memiszero A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
destruct (split_lit (reg cs 10)) as [bb bk] eqn:Hsb.
destruct (split_lit (eaddz (reg cs 2) (-16))) as [qb qk] eqn:Hsq.
destruct (xlo (kn cs) (reg cs 11)) as [nlo|] eqn:Hnlo; [|discriminate].
destruct (xhi (kn cs) (reg cs 11)) as [nhi|] eqn:Hnhi; [|discriminate].
destruct (xhi (kn cs) (reg cs 10)) as [bhi|] eqn:Hbhi; [|discriminate].
destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
apply andb_prop in Hcond as [Hcond Hkz]. apply andb_prop in Hcond as [Hcond Hap].
apply andb_prop in Hcond as [Hcond Hwr]. apply andb_prop in Hcond as [Hcond Hsphi'].
apply andb_prop in Hcond as [Hcond Hsplo']. apply andb_prop in Hcond as [Hcond Hb8].
apply andb_prop in Hcond as [Hn0 Hn40].
apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.leb_le in Hb8. apply Z.leb_le in Hsplo'. apply Z.ltb_lt in Hsphi'.
unfold two64 in Hb8, Hsphi'.

destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
pose proof (w_reg_sound E cs R FULL model 2 HC ltac:(lia)) as R2.
pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hbhi) as Hbhi2.
pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hsplo) as Hsplo2.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hsphi) as Hsphi2.
set (beg := edenot E (reg cs 10)) in *. set (spw := edenot E (reg cs 2)) in *.
set (nw := edenot E (reg cs 11)) in *. set (N := bv_unsigned nw) in *.
pose proof (u64_range nw) as Hnr. fold N in Hnr. pose proof (u64_range beg) as Hbr. pose proof (u64_range spw) as Hsr.
assert (HnwN : Z_to_bv 64 N = nw) by (apply Z_to_bv_bv_unsigned).
assert (HlenN : elenZ E (reg cs 11) = N) by reflexivity.

pose proof (w_split_lit_denot E _ qb qk Hsq) as Hq.
unfold eaddz in Hq. rewrite mkAlu_denot, alu_add in Hq. cbn [edenot] in Hq. fold spw in Hq. unfold v_add in Hq.
destruct (kwritable_sound SEGS E M (kn cs) (kn cs) qb qk 16 HKN HKN Hwr ltac:(lia)) as (Qst & Qlo & Qhi).
set (Q := estart E (SA qb qk)) in *.
assert (HQ : Q = bv_unsigned spw - 16).
{ apply (f_equal bv_unsigned) in Hq. rewrite !u_lit64 in Hq. unfold two64 in Hq.
change (estart E (SA qb qk)) with Q in Hq.
rewrite (Z.mod_small Q) in Hq by lia.
rewrite <- Hq.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
assert (Hstk : store_ok SEGS M (Z_to_bv 64 (bv_unsigned spw - 8)) 8 = true).
{ apply (store_ok_sub M (Z_to_bv 64 Q) 16); rewrite ?u64_lit by lia; try lia. exact Qst. }

pose proof (w_split_lit_denot E (reg cs 10) bb bk Hsb) as Hbeg. fold beg in Hbeg.
destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) bb bk (reg cs 11) HKN HKN Hkz) as (Zb & Blo & Bhi).
rewrite HlenN in Zb, Bhi.
pose proof (ranges_apart_x_sound SEGS E M (kn cs) qb qk (ELit 16) bb bk (reg cs 11) HKN Hap) as Hapart.
rewrite HlenN in Hapart. change (estart E (SA qb qk)) with Q in Hapart.
replace (elenZ E (ELit 16)) with 16 in Hapart by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
set (B := estart E (SA bb bk)) in *.
assert (HuB : bv_unsigned beg = B \/ (B = 2 ^ 64 /\ bv_unsigned beg = 0)).
{ destruct (Z.eq_dec B (2 ^ 64)) as [HB|HB].
- right. split; [exact HB|]. rewrite Hbeg. change (bv_unsigned (edenot E bb) + bk) with B. rewrite HB. reflexivity.
- left. rewrite Hbeg. apply u64_lit. lia. }
assert (Hdisj : bv_unsigned beg + N <= bv_unsigned spw - 8 \/ bv_unsigned spw <= bv_unsigned beg) by lia.
assert (Hz : forall a : word, bv_unsigned beg <= bv_unsigned a < bv_unsigned beg + N ->
rdn SEGS M a 1 = Some [Z_to_bv 8 0]).
{ intros a Ha. apply rdn1_overlay.
destruct HuB as [HuB|[HB Hu0]]; [|lia].
replace a with (Z_to_bv 64 (B + (bv_unsigned a - B))) by (rewrite <- (Z_to_bv_bv_unsigned 64 a) at 2; f_equal; lia).
apply Zb. lia. }
destruct (SUM M beg spw N R (Z_to_bv 64 ret) ltac:(lia) ltac:(lia) ltac:(lia) Hstk Hdisj Hz Hrok R1 R2 R10
ltac:(rewrite HnwN; exact R11)) as (regs' & Hms & Hkept & Ha0).
eapply (call_node_sound cs cs' E R FULL model T ret (Some (ELit 1)) _ regs' _ HC Hn).
- rewrite Hpc. exact Hms.
- exact Hkept.
- exact Ha0.
- eapply w_know_ok_havoc; [exact HKN | | apply wbytes_grows].
intros x Hx. change (estart E (SA qb qk)) with Q in Hx.
replace (elenZ E (ELit 16)) with 16 in Hx by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; reflexivity).
apply wbytes_out; rewrite length_N_to_le_bytes, u64_lit by lia; lia.
- exact Hk.
Qed.

Lemma summary_copy_sound : forall entry,
copy_spec SEGS entry ->
node1_stmt SEGS A nx0 LIMIT USP SINV argH FS0 always (fun cs => summary_copy SEGS A nx0 cs entry).
Proof.
intros entry SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
rewrite summary_copy_eq in Hn.  unfold summary_copy_ref in Hn.
destruct (Z.eqb (pc cs) entry) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
pose proof (w_reg_sound E cs R FULL model 12 HC ltac:(lia)) as R12.
remember (reg cs 12) as ne eqn:Hne.
destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspd.
destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsps.
destruct (xlo (kn cs) ne) as [nlo|] eqn:Hnlo; [|discriminate].
destruct (xhi (kn cs) ne) as [nhi|] eqn:Hnhi; [|discriminate].
destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
destruct (xhi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
apply andb_prop in Hcond as [Hcond Hb2]. apply andb_prop in Hcond as [Hcond Hb1]. apply andb_prop in Hcond as [Hn0 Hn40].
apply Z.leb_le in Hn0. apply Z.leb_le in Hn40. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. unfold two64 in Hb1, Hb2.

destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hnlo) as Hnlo2.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hnhi) as Hnhi2.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi2.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hshi) as Hshi2.
set (s := edenot E (reg cs 10)) in *. set (sr := edenot E (reg cs 11)) in *.
set (nw := edenot E ne) in *. set (n := bv_unsigned nw) in *.
pose proof (u64_range nw) as Hnr. fold n in Hnr. pose proof (u64_range s) as Hsr0. pose proof (u64_range sr) as Hsr1.
assert (Hnwn : Z_to_bv 64 n = nw) by (apply Z_to_bv_bv_unsigned).
pose proof (w_split_lit_denot E (reg cs 10) db dk Hspd) as Hsd. fold s in Hsd.
pose proof (w_split_lit_denot E (reg cs 11) sb sk Hsps) as Hss. fold sr in Hss.
assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
assert (Hsre : Z_to_bv 64 (estart E (SA sb sk)) = sr) by (rewrite Hss; reflexivity).
assert (Hlen : elenZ E ne = n) by reflexivity.

assert (FIN : forall k' bs,
length bs = Z.to_nat n ->
rdn SEGS M sr (length bs) = Some bs ->
store_ok SEGS M s (length bs) = true ->
(bv_unsigned s + n <= bv_unsigned sr \/ bv_unsigned sr + n <= bv_unsigned s) ->
know_ok SEGS E (wbytes M s bs) k' ->
after_call nx0 cs ret (Some (reg cs 10)) k' = Some cs' ->
srealizes SEGS (cfg R (pc cs) FULL model) T).
{ intros k' bs Hlbs Hrd Hst Hdisj HK' Hac.
destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs Hrd Hst Hdisj ltac:(lia) ltac:(lia) Hrok R1 R10 R11
ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) k' regs' _ HC Hac).
- rewrite Hpc. exact Hms.
- exact Hkept.
- exact Ha0.
- exact HK'.
- exact Hk. }

destruct (Z.eqb nhi 0) eqn:Hnhi0.
{ apply Z.eqb_eq in Hnhi0. assert (Hz : n = 0) by lia.
apply (FIN (kn cs) []); [rewrite Hz; reflexivity | reflexivity | reflexivity | lia | cbn [wbytes]; exact HKN | exact Hn]. }
match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
pose proof (k0_sound E M (kn cs) db dk ne (reg cs 10) k0 HKN Hk0) as HK0.
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hwa; [|discriminate] end.
apply andb_prop in Hwa as [Hwr Hap].
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk ne HKN HKN Hwr) as (Wst & Wlo & Whi).
pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk ne sb sk ne HKN Hap) as Hapart.
rewrite Hlen in *.
set (D := estart E (SA db dk)) in *. set (S := estart E (SA sb sk)) in *.
rewrite Hse in Wst.

assert (HAVOC : forall bs, length bs = Z.to_nat n -> 0 < n ->
know_ok SEGS E (wbytes M s bs) (kn_havoc k0 db dk ne)).
{ intros bs Hlbs Hpos.
assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
intros x Hx. rewrite Hlen in Hx. change (estart E (SA db dk)) with D in Hx.
apply wbytes_out; rewrite Hlbs; lia. }

assert (HusD : 0 < n -> 0 <= S -> S + n <= 2 ^ 64 -> bv_unsigned s = D /\ bv_unsigned sr = S).
{ intros Hpos Slo Shi. split; [rewrite <- Hse | rewrite <- Hsre]; apply u64_lit; lia. }

assert (VARS : fresh_ok nx0 cs = true ->
AP.kn_vars_lt (nxt cs) (kn cs) = true /\ AP.expr_vars_lt (nxt cs) db = true /\ AP.expr_vars_lt (nxt cs) ne = true
/\ AP.sr_vars_lt (nxt cs) (s_regs (a_ss cs)) = true).
{ intros Hfresh. destruct (w_fresh_ok_parts cs Hfresh) as (Fsr & Fkn & _).
split; [exact Fkn|]. split; [| split; [rewrite Hne; unfold reg; apply nth_sr_vars_lt'; [exact Fsr | lia] | exact Fsr]].
eapply split_lit_vars; [exact Hspd|]. unfold reg. apply nth_sr_vars_lt'; [exact Fsr | lia]. }

assert (GEN : kwritable_x (kn cs) (kn cs) sb sk ne = true -> flat_x (kn cs) sb sk ne = true ->
forall (W : nat) (u : bool), 8 * Z.of_nat W <= n -> (u = true -> 0 < n) ->
after_call2 nx0 cs ret (Some (reg cs 10))
(map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i))) (seq 0 W)
++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if u then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne)) W
= Some cs' ->
srealizes SEGS (cfg R (pc cs) FULL model) T).
{ intros Hswr Hsfl W u HW Hu Hac.
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hswr) as (SWst & Slo & Shi).
destruct (w_flat_x_sound E M (kn cs) sb sk ne HKN Hsfl) as (_ & _ & Spos).
rewrite Hlen in SWst, Shi. change (bv_unsigned (edenot E ne)) with n in Spos.
change (estart E (SA sb sk)) with S in SWst, Slo, Shi. rewrite Hsre in SWst.
destruct (HusD Spos Slo Shi) as [Hus Husr].
destruct (store_ok_rdn (Z.to_nat n) M sr ltac:(lia) (SWst (Z.to_nat n) ltac:(lia))) as (bs & Hrd & Hlbs).
assert (Hfresh : fresh_ok nx0 cs = true).
{ unfold after_call2 in Hac. destruct (fresh_ok nx0 cs); [reflexivity | cbn [andb] in Hac; discriminate]. }
destruct (VARS Hfresh) as (Fkn & Fdb & Fne & Fsr).
destruct (SUM M s sr n bs R (Z_to_bv 64 ret) ltac:(lia) Hlbs ltac:(rewrite Hlbs; exact Hrd)
ltac:(rewrite Hlbs; apply Wst; lia) ltac:(lia) ltac:(lia) ltac:(lia) Hrok R1 R10 R11
ltac:(rewrite Hnwn; exact R12)) as (regs' & Hms & Hkept & Ha0).
set (vals := map (fun i : nat => Z_to_bv 64 (bytes_le_to_Z (firstn 8 (skipn (8 * i) bs)))) (seq 0 W)).
eapply (call_node_sound2 cs cs' E R FULL model T ret (Some (reg cs 10)) _ W vals regs' (wbytes M s bs) HC Hac).
- rewrite Hpc. exact Hms.
- exact Hkept.
- exact Ha0.
- set (E2 := ext_call2 E (nxt cs) regs' vals).
pose proof (ext_call2_agree E (nxt cs) regs' vals) as Hag2. fold E2 in Hag2.
assert (Edb : edenot E2 db = edenot E db) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fdb]).
assert (Ene : edenot E2 ne = edenot E ne) by (symmetry; eapply edenot_agree'; [exact Hag2 | exact Fne]).
assert (ED2 : estart E2 (SA db dk) = D) by (unfold estart; cbn [a_base a_off]; rewrite Edb; reflexivity).
assert (EL2 : elenZ E2 ne = n) by (unfold elenZ; rewrite Ene; reflexivity).
pose proof (rdn_wbytes_hit SEGS bs M s ltac:(rewrite Hlbs; lia)) as Hhit.
apply Forall_app. split.
+
apply Forall_forall. intros K HinK. apply in_map_iff in HinK as (i & <- & Hini). apply in_seq in Hini.
assert (EDi : estart E2 (SA db (dk + 8 * Z.of_nat i)) = D + 8 * Z.of_nat i).
{ unfold estart. cbn [a_base a_off]. rewrite Edb. change (estart E (SA db dk)) with (bv_unsigned (edenot E db) + dk) in *. unfold D. unfold estart. cbn [a_base a_off]. lia. }
cbn [kentry_ok]. split; [lia|]. split; [unfold flat; rewrite EDi; lia|].
rewrite adenot_SA, EDi. cbn [edenot]. unfold E2. rewrite ext_call2_at by (subst vals; rewrite length_map, length_seq; lia).
subst vals. rewrite (nth_map_seq _ W i (Z_to_bv 64 0)) by lia.
assert (Hpiece : length (firstn 8 (skipn (8 * i) bs)) = 8%nat) by (rewrite length_firstn, length_skipn; lia).
rewrite (word_to_le_bytes_of_bytes_n 8 _ Hpiece) by lia.
pose proof (rdn_skipn SEGS (wbytes M s bs) (length bs) s bs (8 * i) Hhit ltac:(lia)) as Sk.
pose proof (rdn_firstn SEGS (wbytes M s bs) (length bs - 8 * i) _ _ 8 Sk ltac:(lia)) as Fi.
replace (Z_to_bv 64 (D + 8 * Z.of_nat i)) with (s + nat_to_word (8 * i))%bv; [exact Fi|].
apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod, Hus.
rewrite (Z.mod_small (Z.of_nat (8 * i))) by lia. f_equal. lia.
+ apply Forall_app. split.
{
unfold kblob_prefix.
destruct (List.find _ (kn cs)) as [K|] eqn:HF; [|constructor].
apply find_some in HF as [HinK HKt].
destruct K as [| |[kb ko] [n0| | | | | | |] j| | | | | | |]; try (now constructor).
apply andb_prop in HKt as [HKt Hn0le]. apply andb_prop in HKt as [HKt Hn0pos]. apply andb_prop in HKt as [Hkb Hko].
apply expr_eqb_eq in Hkb. apply Z.eqb_eq in Hko. apply Z.ltb_lt in Hn0pos. apply Z.leb_le in Hn0le. subst kb ko.
pose proof (proj1 (Forall_forall _ _) HKN _ HinK) as HKB. cbn [kentry_ok] in HKB.
assert (En0 : elenZ E (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
assert (En0' : elenZ E2 (ELit n0) = n0) by (unfold elenZ; rewrite edenot_lit, u64_lit; lia).
rewrite En0 in HKB. destruct HKB as (Bflat & Blen & Bbytes).
change (estart E (SA sb sk)) with S in Bflat, Bbytes.
destruct Hag2 as [Hag2a Heb2].
assert (HB : kentry_ok SEGS E2 (wbytes M s bs) (KBlob (SA db dk) (ELit n0) j));
[| exact (Forall_cons _ _ _ HB (Forall_nil _)) ].
cbn [kentry_ok]. rewrite En0', ED2, <- Heb2.
refine (conj _ (conj Blen _)).
- unfold flat. rewrite ED2. unfold flat in Bflat. pose proof (Wlo) as Wlo'. pose proof (Whi) as Whi'.
change (estart E (SA db dk)) with D in Wlo', Whi'. lia.
- intros i Hi. rewrite <- Hus.
replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (wbytes_nth bs M s (Z.to_nat i)) by (rewrite ?Hlbs; lia).
f_equal.
pose proof (rdn_nth SEGS M (Z.to_nat n) sr bs (Z.to_nat i) ltac:(lia) Hrd ltac:(lia)) as RB1.
rewrite Husr in RB1. specialize (Bbytes (Z.of_nat (Z.to_nat i)) ltac:(lia)).
cbn [rdn] in RB1. rewrite Bbytes in RB1. injection RB1 as RB1. rewrite ?Nat2Z.id in RB1 |- *. symmetry. exact RB1.
}

assert (HKN2 : know_ok SEGS E2 M (kn cs)) by (eapply know_ok_agree'; [exact Hag2 | exact Fkn | exact HKN]).
pose proof (k0_sound E2 M (kn cs) db dk ne (reg cs 10) k0 HKN2 Hk0) as HK02.
assert (HAV2 : know_ok SEGS E2 (wbytes M s bs) (kn_havoc k0 db dk ne)).
{ eapply w_know_ok_havoc; [exact HK02 | | apply wbytes_grows].
intros x Hx. rewrite ED2, EL2 in Hx. apply wbytes_out; rewrite Hlbs; lia. }
destruct u; [|exact HAV2].
constructor; [|exact HAV2].

apply know_ok_unk_intro_pt.
* unfold flat. rewrite ED2, EL2. specialize (Hu eq_refl). lia.
* intros i Hi. rewrite ED2. rewrite EL2 in Hi. rewrite <- Hus.
replace i with (Z.of_nat (Z.to_nat i)) by lia.
apply wbytes_defined; rewrite Hlbs; lia.
- exact Hk. }

assert (HSRC :
(if (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool
then after_call2 nx0 cs ret (Some (reg cs 10))
(map (fun i : nat => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nxt cs + NCS + i)))
(seq 0 (if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat))
++ kblob_prefix (kn cs) sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: kn_havoc k0 db dk ne else kn_havoc k0 db dk ne))
(if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat)
else None) = Some cs' ->
srealizes SEGS (cfg R (pc cs) FULL model) T).
{ destruct (kwritable_x (kn cs) (kn cs) sb sk ne && flat_x (kn cs) sb sk ne)%bool eqn:Hsw; [|discriminate].
apply andb_prop in Hsw as [Hswr Hsfl].
assert (Hu : Z.ltb 0 nlo = true -> 0 < n) by (intros Hnlo0; apply Z.ltb_lt in Hnlo0; lia).
destruct (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool eqn:HW.
- apply andb_prop in HW as [HW Hp]. apply andb_prop in HW as [HW H256]. apply andb_prop in HW as [Heq Hm8].
apply Z.eqb_eq in Heq. apply Z.eqb_eq in Hm8. apply Z.leb_le in H256. apply Z.ltb_lt in Hp.
apply (GEN Hswr Hsfl); [|exact Hu].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
lia.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
- apply (GEN Hswr Hsfl); [lia | exact Hu]. }

match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hzs end.
{ apply andb_prop in Hzs as [Hpos Hkz]. apply Z.ltb_lt in Hpos.
destruct (kzero_x_sound SEGS E M (kn cs) (kn cs) sb sk ne HKN HKN Hkz) as (Zb & Slo & Shi).
rewrite Hlen in Zb, Shi. change (estart E (SA sb sk)) with S in Zb, Shi, Slo.
destruct (HusD ltac:(lia) Slo Shi) as [Hus Husr].
apply (FIN (KZero (SA db dk) ne :: kn_havoc k0 db dk ne) (repeat (Z_to_bv 8 0) (Z.to_nat n)));
[apply repeat_length | | | lia | | exact Hn].
- rewrite repeat_length. apply rdn_overlay_all; [lia|]. intros i Hi. rewrite Husr. apply Zb. lia.
- rewrite repeat_length. apply Wst. lia.
- constructor; [| apply HAVOC; [apply repeat_length | lia]].
cbn [kentry_ok]. rewrite Hlen. change (estart E (SA db dk)) with D. split; [unfold flat; lia|].
intros i Hi. rewrite <- Hus. apply wbytes_fill_at; lia. }
clear Hzs.

destruct ne as [z| | | | | | |]; try exact (HSRC Hn).
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc3; [|exact (HSRC Hn)] end.
apply andb_prop in Hc3 as [H2048 Hfl]. apply Z.leb_le in H2048.
destruct (copy_facts SEGS (Z.to_nat nhi) (kn cs) sb sk db dk nhi) as [kc|] eqn:Hcf; [|exact (HSRC Hn)].
assert (Hnn : n = nhi).
{ cbn [xhi] in Hnhi. injection Hnhi as <-. rewrite zlit64_eq. subst n nw. cbn [edenot]. apply u_lit64. }
destruct (w_flat_x_sound E M (kn cs) sb sk (ELit z) HKN Hfl) as (Slo & Shi & Spos).
change (estart E (SA sb sk)) with S in Slo, Shi. change (bv_unsigned (edenot E (ELit z))) with n in Shi, Spos.
destruct (HusD Spos Slo Shi) as [Hus Husr].
destruct (copy_facts_sound SEGS E M (kn cs) sb db (Z.to_nat nhi) sk dk nhi kc HKN Hcf ltac:(lia) ltac:(lia)
ltac:(change (estart E (SA sb sk)) with S; lia) ltac:(change (estart E (SA sb sk)) with S; lia)
ltac:(change (estart E (SA db dk)) with D; lia) ltac:(change (estart E (SA db dk)) with D; lia))
as (bs & Hlbs & Hrd & HKC).
change (estart E (SA sb sk)) with S in Hrd. change (estart E (SA db dk)) with D in HKC.
rewrite <- Hnn in Hlbs, Hrd, HKC.
apply (FIN (kc ++ kn_havoc k0 db dk (ELit z)) bs); [exact Hlbs | | | lia | | exact Hn].
- rewrite Hlbs, <- Hsre. exact Hrd.
- rewrite Hlbs. apply Wst. lia.
- apply Forall_app. split.
+ apply HKC. rewrite <- Hus, Z_to_bv_bv_unsigned, <- Hlbs. apply rdn_wbytes_hit. rewrite Hlbs. lia.
+ apply HAVOC; [exact Hlbs | lia].
Qed.

Lemma img_cov_sound : forall E M k a b,
know_ok SEGS E M k -> img_cov k a b = true -> forall i, a <= i < b -> M (Z_to_bv 64 i) = None.
Proof.
intros E M k a b HK H i Hi. unfold img_cov in H. apply existsb_exists in H as [K [HinK HKb]].
destruct K as [| | |lo hi| | | | | |]; try discriminate.
apply andb_prop in HKb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (proj1 (Forall_forall _ _) HK _ HinK) as HK1. cbn [kentry_ok] in HK1. destruct HK1 as (_ & _ & HK1).
apply HK1. lia.
Qed.

Lemma SEALED_BYTES_length : length SEALED_BYTES = 4095%nat.
Proof. reflexivity. Qed.

Lemma SEALED_W_bytes : word_to_le_bytes 8 (Z_to_bv 64 SEALED_W) = firstn 8 SEALED_BYTES.
Proof.
replace SEALED_W with (bytes_le_to_Z (firstn 8 SEALED_BYTES)) by (vm_compute; reflexivity).
apply word_to_le_bytes_of_bytes_n; reflexivity.
Qed.

Lemma SEALED_BYTES_nth_hi : forall j, (8 <= j < 4095)%nat -> nth j SEALED_BYTES (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
intros j Hj. unfold SEALED_BYTES. rewrite app_nth2 by (cbn; lia). cbn [length]. apply nth_repeat_lt. lia.
Qed.

Lemma summary_istrncpy_sound :
istrncpy_spec SEGS (x_istrncpy A) (x_sealed A) ->
node1_stmt SEGS A nx0 LIMIT USP SINV argH FS0 always (fun cs => summary_istrncpy A nx0 cs).
Proof.
intros SUM cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
rewrite summary_istrncpy_eq in Hn.  unfold summary_istrncpy_ref in Hn.
destruct (Z.eqb (pc cs) (x_istrncpy A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
destruct (reg_lit cs 11) as [src|] eqn:H11; [|discriminate].
destruct (reg_lit cs 12) as [n|] eqn:H12; [|discriminate].
destruct (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool eqn:Hsn; [|discriminate]. cbn [negb] in Hn.
apply andb_prop in Hsn as [Hsrc Hn95]. apply Z.eqb_eq in Hsrc. apply Z.eqb_eq in Hn95. subst src n.
destruct (split_lit (reg cs 10)) as [db dk] eqn:Hspl.
destruct (xhi (kn cs) (reg cs 10)) as [dhi|] eqn:Hdhi; [|discriminate].
match type of Hn with (match ?o with _ => _ end) = _ => destruct o as [k0|] eqn:Hk0; [|discriminate] end.
match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
rename Hcond into Hb. apply Z.ltb_lt in Hb. unfold two64 in Hb.
match goal with Hl : Z.leb 0 (x_sealed A) = true |- _ => apply Z.leb_le in Hl; rename Hl into Hs0 end.
match goal with Hl : Z.ltb (x_sealed A + 9) two64 = true |- _ => apply Z.ltb_lt in Hl; unfold two64 in Hl; rename Hl into Hs9 end.
match goal with Hl : kwritable_x _ _ db dk (ELit 4095) = true |- _ => rename Hl into Hwr end.
match goal with Hl : img_cov k0 _ _ = true |- _ => rename Hl into Hcov end.
match goal with Hl : ranges_apart_x _ db dk (ELit 4095) (ELit 0) _ (ELit 9) = true |- _ => rename Hl into Hap end.

destruct (ret_lit_sound E cs R FULL model ret HC Hret) as (R1 & Hrok & Hretr).
destruct (w_reg_lit_sound E cs R FULL model 11 _ HC ltac:(lia) H11) as [R11 _].
destruct (w_reg_lit_sound E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 _].
pose proof (w_reg_sound E cs R FULL model 10 HC ltac:(lia)) as R10.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Hdhi) as Hdhi'.
set (s := edenot E (reg cs 10)) in *.
pose proof (w_split_lit_denot E (reg cs 10) db dk Hspl) as Hsd. fold s in Hsd.
assert (Hse : Z_to_bv 64 (estart E (SA db dk)) = s) by (rewrite Hsd; reflexivity).
pose proof (k0_sound E M (kn cs) db dk (ELit 4095) (reg cs 10) k0 HKN
ltac:(destruct (off_image_x A (kn cs) db dk (ELit 4095)); [exact Hk0 | destruct (reg cs 10); try discriminate; exact Hk0])) as HK0.
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) db dk (ELit 4095) HKN HKN Hwr) as (Wst & Wlo & Whi).
pose proof (ranges_apart_x_sound SEGS E M (kn cs) db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9) HKN Hap) as Hapart.
rewrite !elenZ_lit in * by lia.
unfold estart in Hapart at 2 3; cbn [a_base a_off edenot] in Hapart. rewrite u_lit0 in Hapart.
set (D := estart E (SA db dk)) in *.
assert (Hus : bv_unsigned s = D) by (rewrite <- Hse; apply u64_lit; lia).
pose proof (img_cov_sound E M k0 _ _ HK0 Hcov) as Hnone.
destruct (SUM M s R (Z_to_bv 64 ret) Hnone ltac:(rewrite <- Hse; apply Wst; lia) ltac:(lia) ltac:(lia)
Hrok R1 R10 R11 R12) as (regs' & Hms & Hkept & Ha0).
eapply (call_node_sound cs cs' E R FULL model T ret (Some (reg cs 10)) _ regs' _ HC Hn).
- rewrite Hpc. exact Hms.
- exact Hkept.
- exact Ha0.
- set (M' := wbytes M s SEALED_BYTES).
assert (Hlen : bv_unsigned s + Z.of_nat (length SEALED_BYTES) <= 2 ^ 64) by (rewrite SEALED_BYTES_length; lia).
assert (BY : forall j, (j < 4095)%nat -> M' (Z_to_bv 64 (D + Z.of_nat j)) = Some (nth j SEALED_BYTES (Z_to_bv 8 0))).
{ intros j Hj. subst M'. rewrite <- Hus. apply wbytes_nth; [exact Hlen | rewrite SEALED_BYTES_length; exact Hj]. }
constructor; [|constructor].
+
cbn [kentry_ok]. split; [lia|]. split; [unfold flat; cbn [Z.of_nat]; fold D; lia|].
rewrite adenot_SA. fold D. rewrite <- Hus, Z_to_bv_bv_unsigned.
cbn [edenot]. rewrite SEALED_W_bytes.
replace (firstn 8 SEALED_BYTES) with (map (fun j => nth j SEALED_BYTES (Z_to_bv 8 0)) (seq 0 8)) by reflexivity.
apply rdn_of_nth; [lia|]. intros j Hj. apply rdn1_overlay. rewrite Hus. apply BY. lia.
+
cbn [kentry_ok]. rewrite elenZ_lit by lia.
assert (HD8 : estart E (SA db (dk + 8)) = D + 8) by (unfold D, estart; cbn [a_base a_off]; lia).
rewrite HD8. split; [unfold flat; lia|].
intros i Hi. replace (D + 8 + i) with (D + Z.of_nat (Z.to_nat (8 + i))) by lia.
rewrite BY by lia. f_equal. apply SEALED_BYTES_nth_hi. lia.
+
eapply w_know_ok_havoc; [exact HK0 | | apply wbytes_grows].
intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite ?SEALED_BYTES_length; lia.
- exact Hk.
Qed.

Lemma firstn_skipn_map_nth : forall {T} (d : T) k (l : list T) m, (m + k <= length l)%nat ->
firstn k (skipn m l) = map (fun q => nth (m + q)%nat l d) (seq 0 k).
Proof.
intros T d k. induction k as [|k IH]; intros l m Hm; [reflexivity|].
cbn [seq map]. rewrite <- seq_shift, map_map.
destruct (skipn m l) as [|x rest] eqn:Hs.
- exfalso. pose proof (f_equal (@length _) Hs) as HL. rewrite length_skipn in HL. cbn in HL. lia.
- cbn [firstn]. f_equal.
+ rewrite <- nth_skipn, Hs. reflexivity.
+ replace rest with (skipn (S m) l).
2: { replace (S m) with (1 + m)%nat by lia. rewrite <- skipn_skipn, Hs. reflexivity. }
rewrite (IH l (S m)) by lia. apply map_ext. intros q. f_equal. lia.
Qed.

Lemma popfree_facts_sound : forall E M lb lk cnt c s K (base : word),
bv_unsigned base = estart E (SA lb lk) ->
(K <= Z.to_nat cnt)%nat -> 0 < cnt -> estart E (SA lb lk) + 4 * cnt <= 2 ^ 64 -> 0 <= estart E (SA lb lk) ->
know_ok SEGS E (wbytes M base (pf_bytes c s (Z.to_nat cnt))) (popfree_facts lb lk cnt c s K).
Proof.
intros E M lb lk cnt c s K base Hbase HK Hcnt Hhi Hlo. unfold popfree_facts. apply Forall_forall. intros Kx Hin.
apply in_map_iff in Hin as [t [<- Hint]]. apply in_seq in Hint.
set (D := estart E (SA lb lk)) in *. set (j := cnt - 1 - Z.of_nat t).
assert (Hj : 0 <= j < cnt) by lia.
cbn [kentry_ok]. split; [lia|].
assert (HDj : estart E (SA lb (lk + 4 * j)) = D + 4 * j) by (unfold D, estart; cbn [a_base a_off]; lia).
split; [unfold flat; rewrite HDj; cbn [Z.of_nat]; lia|].
rewrite adenot_SA, HDj. cbn [edenot].
rewrite word_to_le_bytes4_Z.
replace ((c + Z.of_nat t * s) / 16) with ((c + (Z.of_nat (Z.to_nat cnt) - 1 - j) * s) / 16) by (f_equal; f_equal; lia).
rewrite <- (pf_bytes_cell c s (Z.to_nat cnt) j) by lia.
assert (Hlen : length (pf_bytes c s (Z.to_nat cnt)) = (4 * Z.to_nat cnt)%nat) by apply pf_bytes_length.
rewrite (firstn_skipn_map_nth (Z_to_bv 8 0) 4) by (rewrite Hlen; lia).
assert (Hu : bv_unsigned (Z_to_bv 64 (D + 4 * j)) = D + 4 * j) by (apply u64_lit; lia).
apply rdn_of_nth; [rewrite Hu; lia|]. intros q Hq. apply rdn1_overlay. rewrite Hu.
replace (D + 4 * j + Z.of_nat q) with (bv_unsigned base + Z.of_nat (Z.to_nat (4 * j) + q)) by lia.
apply wbytes_nth; rewrite Hlen; lia.
Qed.

Lemma summary_popfree_sound :
popfree_spec SEGS (x_popfree A) ->
forall args, node1_stmt SEGS A nx0 LIMIT USP SINV argH FS0 always (fun cs => summary_popfree A nx0 cs args).
Proof.
intros SUM args cs cs' E R FULL model T HC _ Hn Hk.
pose proof HC as HKN. apply co_know in HKN.
set (M := MR E cs model FULL) in *.
unfold summary_popfree in Hn.
destruct (Z.eqb (pc cs) (x_popfree A)) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
destruct args as [|[K| | | | | | |] [|]]; try discriminate.
destruct (reg_lit cs 10) as [i|] eqn:H10; [|discriminate].
destruct (reg_lit cs 12) as [c|] eqn:H12; [|discriminate].
destruct (reg_lit cs 21) as [s|] eqn:H21; [|discriminate].
destruct (reg_lit cs 19) as [n|] eqn:H19; [|discriminate].
destruct (split_lit (eaddz (reg cs 11) (- (4 * n)))) as [lb lk] eqn:Hspl.
destruct (xlo (kn cs) (reg cs 11)) as [el|] eqn:Hel; [|discriminate].
destruct (xhi (kn cs) (reg cs 11)) as [eh|] eqn:Heh; [|discriminate].
match type of Hn with (if ?cnd then _ else _) = _ => destruct cnd eqn:Hcond; [|discriminate] end.
repeat match type of Hcond with (_ && _)%bool = true => apply andb_prop in Hcond as [Hcond ?X] end.
apply Z.leb_le in Hcond.
repeat match goal with
| Hl : Z.leb _ _ = true |- _ => apply Z.leb_le in Hl
| Hl : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hl end.
repeat match goal with Hl : context [two64] |- _ => change two64 with (2 ^ 64)%Z in Hl end.
match goal with Hl : fresh_ok nx0 cs = true |- _ => rename Hl into Hfresh end.
match goal with Hl : kwritable_x _ _ lb lk _ = true |- _ => rename Hl into Hwr end.
match type of Hn with Some ?x = Some _ => assert (Hcs : cs' = x) by congruence end. subst cs'. clear Hn.

destruct (w_reg_lit_sound E cs R FULL model 10 _ HC ltac:(lia) H10) as [R10 Hi].
destruct (w_reg_lit_sound E cs R FULL model 12 _ HC ltac:(lia) H12) as [R12 Hc].
destruct (w_reg_lit_sound E cs R FULL model 21 _ HC ltac:(lia) H21) as [R21 Hs].
destruct (w_reg_lit_sound E cs R FULL model 19 _ HC ltac:(lia) H19) as [R19 Hnn].
pose proof (w_reg_sound E cs R FULL model 11 HC ltac:(lia)) as R11.
pose proof (xlo_sound SEGS E M (kn cs) _ _ HKN Hel) as Hel'.
pose proof (xhi_sound SEGS E M (kn cs) _ _ HKN Heh) as Heh'.
repeat match goal with Hl : context [two64] |- _ => change two64 with (2 ^ 64)%Z in Hl end.
set (ew := edenot E (reg cs 11)) in *. set (e := bv_unsigned ew) in *.
pose proof (u64_range ew) as Her. fold e in Her.
set (cnt := n - i) in *.
destruct (kwritable_x_sound SEGS E M (kn cs) (kn cs) lb lk (ELit (4 * cnt)) HKN HKN Hwr) as (Wst & Wlo & Whi).
rewrite elenZ_lit in Wst, Whi by lia.
set (D := estart E (SA lb lk)) in *.
pose proof (w_split_lit_denot E _ lb lk Hspl) as Hsd.
assert (HloD : edenot E (eaddz (reg cs 11) (- (4 * n))) = Z_to_bv 64 (e - 4 * n)).
{ unfold eaddz. rewrite mkAlu_denot. cbn [edenot]. apply bv_eq. rewrite u_add64. fold ew. rewrite u_lit64. unfold two64.
rewrite u64_lit by lia. fold e.
replace (e + - (4 * n) mod 2 ^ 64) with ((e - 4 * n) + 1 * 2 ^ 64).
2: { rewrite <- (Z.mod_add (- (4 * n)) 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (HD : D = e - 4 * n).
{ assert (HDdef : D = bv_unsigned (edenot E lb) + lk) by reflexivity.
rewrite HloD, <- HDdef in Hsd. apply (f_equal bv_unsigned) in Hsd. rewrite !u64_lit in Hsd by lia. lia. }
destruct (SUM R M i e c s n R10 ltac:(unfold e; rewrite Z_to_bv_bv_unsigned; exact R11) R12 R21 R19
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(rewrite <- HD; apply Wst; lia)) as (regs' & Hms & G10 & G12 & G14 & G15 & Gkeep).
set (M' := wbytes M (Z_to_bv 64 (e - 4 * n)) (pf_bytes c s (Z.to_nat (n - i)))) in *.
eapply (call_core cs E E R FULL model T (pc cs + 32) _ _ (nxt cs) regs' M' HC Hfresh (env_agree_refl _ _)).

4: { intros R' FULL' model' HC' Hfs. apply (Hk E R' FULL' model' (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' Hfs). }
- rewrite Hpc. exact Hms.
-
apply regs_ok_pointwise. intros r Hr0. rewrite !nth_sr_upd.
pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ _ HC r) as HR. unfold sr_get in HR.
assert (Hrz : bv_eqb r 0%bv = false).
{ unfold bv_eqb. apply Z.eqb_neq. intros Hc0. apply Hr0. apply bv_eq. exact Hc0. }
rewrite Hrz in HR.
destruct (Nat.eqb (ridx r) 15) eqn:E15.
{ apply Nat.eqb_eq in E15. rewrite (reg_of_ridx r 15 E15). refine (eq_trans G15 _). rewrite HloD. reflexivity. }
destruct (Nat.eqb (ridx r) 14) eqn:E14.
{ apply Nat.eqb_eq in E14. rewrite (reg_of_ridx r 14 E14). refine (eq_trans G14 _). cbn [edenot]. f_equal; f_equal; lia. }
destruct (Nat.eqb (ridx r) 12) eqn:E12.
{ apply Nat.eqb_eq in E12. rewrite (reg_of_ridx r 12 E12). refine (eq_trans G12 _). cbn [edenot]. f_equal; lia. }
destruct (Nat.eqb (ridx r) 10) eqn:E10.
{ apply Nat.eqb_eq in E10. rewrite (reg_of_ridx r 10 E10). refine (eq_trans G10 _). reflexivity. }
apply Nat.eqb_neq in E15. apply Nat.eqb_neq in E14. apply Nat.eqb_neq in E12. apply Nat.eqb_neq in E10.
rewrite Gkeep; [exact HR| | | |]; intros Hrr; [apply E10 | apply E12 | apply E14 | apply E15]; rewrite Hrr; reflexivity.
-
assert (Hlen : length (pf_bytes c s (Z.to_nat (n - i))) = (4 * Z.to_nat cnt)%nat) by (unfold cnt; apply pf_bytes_length).
assert (Hbase : bv_unsigned (Z_to_bv 64 (e - 4 * n)) = D) by (rewrite HD; apply u64_lit; lia).
unfold know_ok. apply Forall_app_intro; [|apply Forall_app_intro].
+ fold cnt. apply (popfree_facts_sound E M lb lk cnt c s (Z.to_nat K) (Z_to_bv 64 (e - 4 * n)) Hbase); lia.
+ destruct (Z.ltb K cnt) eqn:HKc; [|constructor]. apply Z.ltb_lt in HKc.
constructor; [|constructor]. cbn [kentry_ok]. rewrite elenZ_lit by lia. split; [unfold flat; lia|].
intros q Hq. fold D. replace (D + q) with (bv_unsigned (Z_to_bv 64 (e - 4 * n)) + Z.of_nat (Z.to_nat q)) by lia.
subst M'. apply wbytes_defined; rewrite Hlen; lia.
+ eapply w_know_ok_havoc; [exact HKN | | apply wbytes_grows].
intros x Hx. rewrite elenZ_lit in Hx by lia. fold D in Hx. subst M'. apply wbytes_out; rewrite Hlen; lia.
Qed.

Theorem node_x_sound_XIMemset :
fill_spec SEGS (x_imemset A) 256 -> x_stmt SEGS A nx0 LIMIT USP SINV argH FS0 XIMemset.
Proof. intros SUM args. exact (summary_fill_sound _ _ SUM). Qed.

Theorem node_x_sound_XMemset :
fill_spec SEGS (x_memset A) two64 -> x_stmt SEGS A nx0 LIMIT USP SINV argH FS0 XMemset.
Proof. intros SUM args. exact (summary_fill_sound _ _ SUM). Qed.

Theorem node_x_sound_XIMemcpy :
copy_spec SEGS (x_imemcpy A) -> x_stmt SEGS A nx0 LIMIT USP SINV argH FS0 XIMemcpy.
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.

Theorem node_x_sound_XMemcpy :
copy_spec SEGS (x_memcpy A) -> x_stmt SEGS A nx0 LIMIT USP SINV argH FS0 XMemcpy.
Proof. intros SUM args. exact (summary_copy_sound _ SUM). Qed.

Theorem node_x_sound_XMemIsZero :
miz_spec SEGS (x_memiszero A) -> x_stmt SEGS A nx0 LIMIT USP SINV argH FS0 XMemIsZero.
Proof. intros SUM args. exact (summary_miz_sound SUM). Qed.

Theorem node_x_sound_XIStrncpy :
istrncpy_spec SEGS (x_istrncpy A) (x_sealed A) -> x_stmt SEGS A nx0 LIMIT USP SINV argH FS0 XIStrncpy.
Proof. intros SUM args. exact (summary_istrncpy_sound SUM). Qed.

Theorem node_x_sound_XPopFree :
popfree_spec SEGS (x_popfree A) -> x_stmt SEGS A nx0 LIMIT USP SINV argH FS0 XPopFree.
Proof. intros SUM args. exact (summary_popfree_sound SUM args). Qed.

End Sound.

End APSX.
End Mq3.

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Import EdStepA.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWXq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWXq.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQny.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQny. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgpE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgpE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU0c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU0c. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qo8J.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qo8J.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHup.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qek8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qek8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHup.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6EJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6EJ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG64.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG64.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q85Z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q85Z.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QND5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QND5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBCP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBCP.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6EJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6EJ.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsSk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsSk. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3bI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3bI.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt8n.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt8n. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWtD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWtD. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqZL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqZL.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDlz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDlz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOTP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOTP. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1LT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1LT.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQny.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQny.Mq0.
Local Instance asanreflect_fx : QWTC.FPState := QWTC.fx0.
Import ListNotations.
Open Scope bv_scope.

Section Noacc.
Variable segs : list Segment.

Lemma sstep_of_check_noacc : forall ms model x8 eff m' evs,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff ->
m_halted m' = None ->
syscall_effect_accesses eff = [] ->
sstep_cfg segs (alloc_only_cfg false) (mkCfg ms model) evs (SNext (mkCfg (advance_past_svc (apply_effect ms eff)) m')).
Proof.
intros ms model x8 eff m' evs Hh Hsvc Hc Hns Hh' Hacc.
apply (sstep_cfg_syscall segs (alloc_only_cfg false) ms model x8 eff m' m' evs Hh Hsvc).
- apply check_syscall_ok_iff. exact Hc.
- exact Hns.
- exact Hh'.
- rewrite Hacc. apply materialize_model_accesses_nil.
Qed.

Lemma node_chk_ev_noacc : forall ms model x8 (I : Type)
(effs : I -> SyscallEffect) (ms' : I -> Model) (evs : I -> list event),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) (evs i)) ->
(forall i, ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (effs i)) ->
(forall eff m' ev, check_syscall (sys_input segs ms x8) eff model = CheckOk m' ev ->
(exists i, eff = effs i /\ m' = ms' i /\ ev = evs i)
\/ (spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, syscall_effect_accesses (effs i) = []) ->
node_ok segs (mkCfg ms model) I evs
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' evs Hh Hsvc Hok Hns Hinv Hnu Hh' Hacc. split.
- intros i. apply (sstep_of_check_noacc ms model x8);
[exact Hh | exact Hsvc | exact (Hok i) | exact (Hns i) | exact (Hh' i) | exact (Hacc i)].
- intros e st Hss.
destruct (sstep_cfg_svc_inv segs ms model x8 e st Hsvc Hss)
as [(eff & model' & ev & Hc & [(m'' & Hnsp & Hh2 & -> & Hmat & ->) | [(Hnsp & Hh2 & -> & Hmat & ->) | (code & Hh2 & -> & ->)]])
| (eff & Hc & -> & ->)].
+ destruct (Hinv _ _ _ Hc) as [(i & -> & -> & ->) | [Hsp _]]; [| contradiction].
rewrite (Hacc i), materialize_model_accesses_nil in Hmat.
injection Hmat as <-. exists i. split; reflexivity.
+ destruct (Hinv _ _ _ Hc) as [(i & -> & -> & ->) | [Hsp _]]; [| contradiction].
rewrite (Hacc i), materialize_model_accesses_nil in Hmat. discriminate.
+ destruct (Hinv _ _ _ Hc) as [(i & -> & -> & ->) | [_ Hh3]].
* rewrite Hh' in Hh2. discriminate.
* rewrite Hh3 in Hh2. discriminate.
+ exfalso. exact (Hnu eff Hc).
Qed.

Lemma node_chk_noacc : forall ms model x8 (I : Type) (effs : I -> SyscallEffect) (ms' : I -> Model),
m_halted model = None -> ms_svc_pending ms = Some x8 ->
(forall i, check_syscall (sys_input segs ms x8) (effs i) model = CheckOk (ms' i) []) ->
(forall i, ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model (effs i)) ->
(forall eff m' evs, check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
(exists i, eff = effs i /\ m' = ms' i /\ evs = [])
\/ (spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
(forall i, m_halted (ms' i) = None) ->
(forall i, syscall_effect_accesses (effs i) = []) ->
node_ok segs (mkCfg ms model) I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (effs i))) (ms' i)).
Proof.
intros ms model x8 I effs ms' Hh Hsvc Hok Hns Hinv Hnu Hh' Hacc.
apply (node_chk_ev_noacc ms model x8 I effs ms' (fun _ => []) Hh Hsvc Hok Hns); auto.
Qed.

Lemma node_det_noacc : forall ms model x8 eff0 m0 evs0,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
check_syscall (sys_input segs ms x8) eff0 model = CheckOk m0 evs0 ->
~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff0 ->
(forall eff m' evs,
check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
(eff = eff0 /\ m' = m0 /\ evs = evs0)
\/ (spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
m_halted m0 = None ->
syscall_effect_accesses eff0 = [] ->
node_ok segs (mkCfg ms model) unit (fun _ => evs0)
(fun _ => mkCfg (advance_past_svc (apply_effect ms eff0)) m0).
Proof.
intros ms model x8 eff0 m0 evs0 Hh Hsvc Hok0 Hns0 Hchk Hnu Hh0 Hacc.
apply (node_chk_ev_noacc ms model x8 unit (fun _ => eff0) (fun _ => m0) (fun _ => evs0) Hh Hsvc).
- intros []. exact Hok0.
- intros []. exact Hns0.
- intros eff m' ev Hc. destruct (Hchk eff m' ev Hc) as [(-> & -> & ->) | Hsp];
[left; exists tt; auto | right; exact Hsp].
- exact Hnu.
- intros []; exact Hh0.
- intros []; exact Hacc.
Qed.

Lemma srz_det_noacc : forall ms model x8 eff0 m0 T,
m_halted model = None ->
ms_svc_pending ms = Some x8 ->
check_syscall (sys_input segs ms x8) eff0 model = CheckOk m0 [] ->
~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff0 ->
(forall eff m' evs,
check_syscall (sys_input segs ms x8) eff model = CheckOk m' evs ->
(eff = eff0 /\ m' = m0 /\ evs = [])
\/ (spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model eff /\ m_halted m' = None)) ->
(forall eff, check_syscall (sys_input segs ms x8) eff model <> CheckUnmodeled) ->
m_halted m0 = None ->
syscall_effect_accesses eff0 = [] ->
srealizes segs (mkCfg (advance_past_svc (apply_effect ms eff0)) m0) T ->
srealizes segs (mkCfg ms model) T.
Proof.
intros ms model x8 eff0 m0 T Hh Hsvc Hok0 Hns0 Hchk Hnu Hh0 Hacc Hc.
eapply srz_silent1; [eapply node_det_noacc; eassumption | exact Hc].
Qed.

Lemma srz_cases : forall c (I : Type) (nx : I -> config) (T : I -> TSet) (i0 : I),
node_ok segs c I (fun _ => []) nx ->
(forall i, srealizes segs (nx i) (T i)) ->
srealizes segs c (t_alt T).
Proof.
intros c I nx T i0 Hnode Hc.
apply (srz_conseq segs c (t_alt (fun i => t_emit [] (T i)))).
- apply (srz_node segs c I (fun _ => []) nx T i0 Hnode Hc).
- intros tr. split.
+ intros [i Hi]. exists i.
exact (proj1 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
+ intros [i Hi]. exists i.
exact (proj2 (t_emit_nil_eq (T i) (srealizes_nonempty segs _ _ (Hc i)) tr) Hi).
Qed.

Lemma forget_vm_ranges_halted : forall ranges m,
m_halted (forget_vm_ranges ranges m) = m_halted m.
Proof.
induction ranges as [|[a n] r IH]; intros m; [reflexivity|].
cbn [forget_vm_ranges]. rewrite IH. apply vm_forget_range_halted.
Qed.

Lemma brk_model_halted : forall req r m, m_halted (brk_model req r m) = m_halted m.
Proof.
intros. unfold brk_model, with_brk_next. cbv zeta.
rewrite forget_vm_ranges_halted. apply with_vmmaps_halted.
Qed.

Lemma stepacc_ecall_epend : forall regs pc mem rom w,
fetch_word segs pc = Some w -> is_ecall w = true ->
RiscvSemantics.step_accesses segs (mkst regs pc mem rom)
= MachineOk (@mkAccessReport machine_state (epend regs pc mem rom (getr regs 17)) []).
Proof.
intros regs pc mem rom w Hfetch Hecall.
unfold RiscvSemantics.step_accesses. cbn [ms_pc ms_pc_val mkst].
rewrite Hfetch. cbv beta iota.
unfold RiscvSemantics.decode_exec_accesses. rewrite Hecall. cbv beta iota.
reflexivity.
Qed.

Lemma node_instr_noacc : forall ms model ms',
m_halted model = None ->
ms_svc_pending ms = None ->
RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
node_ok segs (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg ms' model).
Proof.
intros ms model ms' Hh Hsvc Hstep.
assert (Hacc : mi_account_step segs ms model = MachineOk (ms', model)).
{ unfold mi_account_step. rewrite Hstep. cbn [accessed_ranges access_value].
rewrite materialize_model_accesses_nil. reflexivity. }
split.
- intros []. apply (sstep_cfg_instr segs (alloc_only_cfg false) ms model ms' model Hh Hsvc Hacc).
- intros e st Hss. exists tt. apply sstep_cfg_sub in Hss.
inversion Hss; subst;
match goal with
| H : mi_account_step segs ms model = _ |- _ => rewrite Hacc in H; try discriminate; injection H as <- <-; split; reflexivity
| H : ms_svc_pending ms = Some _ |- _ => rewrite Hsvc in H; discriminate
end.
Qed.

Lemma srz_sys_lazy : forall regs pc mem rom model w T,
m_halted model = None ->
fetch_word segs pc = Some w -> is_ecall w = true ->
srealizes segs (mkCfg (epend regs pc mem rom (getr regs 17)) model) T ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) T.
Proof.
intros regs pc mem rom model w T Hh HF HE Hc.
eapply srz_silent1; [| exact Hc].
apply node_instr_noacc; [exact Hh | reflexivity | eapply stepacc_ecall_epend; eassumption].
Qed.

Lemma srz_munmap_lazy : forall regs (pc : word) mem rom model w (a : word) (len : Z) K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 215 ->
getr regs 10 = a -> (bv_unsigned a mod page_size = 0)%Z ->
getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned a + page_round_up_Z len <= TASK_SIZE)%Z ->
map_has (vm_maps (m_vmmaps model)) a (Z_to_bv 64 (page_round_up_Z len)) = true ->
srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 0)) (v_addi pc 4)
(unfill a (Z_to_bv 64 (page_round_up_Z len)) mem) rom)
(munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model)) K ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
intros regs pc mem rom model w a len K HF HE Hh H17 H10 Hal H11 Hlen Hnw Hhas Hc.
assert (Hlen' : (len < two_pow_64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range a). unfold TASK_SIZE, two_pow_64 in *. lia. }
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 215%Z) by (rewrite H17; apply u64_lit; lia).
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len).
{ unfold ms. rewrite ms_gpr_epend1, H11. apply u64_lit. unfold two_pow_64 in Hlen'. lia. }
assert (Hpr : page_round_up (ms_gpr ms 1) = Z_to_bv 64 (page_round_up_Z len)).
{ unfold page_round_up. rewrite Hu1. reflexivity. }
assert (H0 : ms_gpr ms 0 = a) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hargs : munmap_args_ok ms model).
{ unfold munmap_args_ok. rewrite H0, Hu1, Hpr. repeat split; try assumption.
intro Hz. apply (f_equal bv_unsigned) in Hz. rewrite Hu1 in Hz.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hz. lia. }
pose proof (fun eff => eq_trans (munmap_check segs ms (getr regs 17) model eff Hno) (munmap_check_modeled ms model eff Hargs)) as Hchk.
rewrite H0, Hpr in Hchk.
eapply (srz_det_noacc ms model (getr regs 17)
(mkEffectU (Z_to_bv 64 0) [] [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [])
(munmap_model a (Z_to_bv 64 (page_round_up_Z len)) model));
[exact Hh | reflexivity | | | | | | reflexivity |].
- rewrite Hchk. unfold w_is0. rewrite bv_eqb_refl.
rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
- apply (ns_sysno_eq _ _ _ 215%Z); [exact Hno | reflexivity].
- intros eff m' evs Hck. left. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (w_is0 r) eqn:E0; [|discriminate].
destruct (listNN_eqb us [(a, Z_to_bv 64 (page_round_up_Z len))]) eqn:Hl; [|discriminate].
apply listNN_eqb_eq in Hl. subst us. cbn [andb] in Hck. injection Hck as <- <-.
unfold w_is0 in E0. apply bv_eqb_eq in E0. subst r. repeat split; reflexivity.
- intros eff Hck. rewrite Hchk in Hck. destruct eff as [r ws zs us cs ci].
destruct ws; [|discriminate]. destruct zs; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (w_is0 r && listNN_eqb us _)%bool; discriminate.
- rewrite munmap_model_halted. exact Hh.
- unfold ms. rewrite adv_unmaps1_epend. exact Hc.
Qed.

Lemma node_brk_lazy : forall ms model x8 (P : word -> Prop),
m_halted model = None ->
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 214%Z ->
(forall r, P r -> brk_resolution_ok model (ms_gpr ms 0) r) ->
(forall r, P r -> ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model
(mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
(brk_unmaps r (vm_brk (m_vmmaps model))) [] [])) ->
(forall r, brk_resolution_ok model (ms_gpr ms 0) r -> P r
\/ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model
(mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
(brk_unmaps r (vm_brk (m_vmmaps model))) [] [])) ->
node_ok segs (mkCfg ms model)
{r : word | P r}
(fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms
(mkEffectU (proj1_sig i) []
(brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
(brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])))
(brk_model (ms_gpr ms 0) (proj1_sig i) model)).
Proof.
intros ms model x8 P Hh Hsvc Hno HPok HPns HPall.
apply (node_chk_noacc ms model x8 {r : word | P r}
(fun i => mkEffectU (proj1_sig i) []
(brk_zeros (ms_gpr ms 0) (proj1_sig i) (vm_brk (m_vmmaps model)))
(brk_unmaps (proj1_sig i) (vm_brk (m_vmmaps model))) [] [])
(fun i => brk_model (ms_gpr ms 0) (proj1_sig i) model) Hh Hsvc).
- intros [r Hr]. cbn [proj1_sig]. apply check_syscall_ok_iff.
exact (brk_ok_intro segs ms x8 model r Hno (HPok r Hr)).
- intros [r Hr]. cbn [proj1_sig]. exact (HPns r Hr).
- intros eff m' evs Hc. apply check_syscall_ok_iff in Hc.
apply (brk_ok_iff segs ms x8 model eff m' evs Hno) in Hc as (Heff & -> & Hok & ->).
destruct (HPall _ Hok) as [HP | Hsp].
+ left. exists (exist _ (eff_ret eff) HP). cbn [proj1_sig]. rewrite <- Heff. repeat split; reflexivity.
+ right. split; [rewrite Heff; exact Hsp | rewrite brk_model_halted; exact Hh].
- intros eff Hc. apply (brk_no_unmodeled segs ms x8 model Hno).
exact (proj1 (check_syscall_err_iff _ _ _) Hc).
- intros [r Hr]. cbn [proj1_sig]. rewrite brk_model_halted. exact Hh.
- intros [r Hr]. reflexivity.
Qed.

Lemma brk_ns_unique : forall ms model x8 (b : word),
bv_unsigned x8 = 214%Z ->
(forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b) ->
forall r, brk_resolution_ok model (ms_gpr ms 0) r ->
~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms x8) model
(mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
(brk_unmaps r (vm_brk (m_vmmaps model))) [] []).
Proof.
intros ms model x8 b Hno Hcases r Hr. apply ns_same_ret. intros eff' m' evs' Hs.
apply (brk_ok_iff segs ms x8 model eff' m' evs' Hno) in Hs as (_ & _ & Hok & _).
cbn [eff_ret]. rewrite (proj1 (Hcases _) Hok), (proj1 (Hcases _) Hr). reflexivity.
Qed.

Lemma srz_brk_query_lazy : forall regs (pc : word) mem rom model w K,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 214 ->
getr regs 10 = Z_to_bv 64 0 ->
srealizes segs (mkCfg (mkst (regupd regs 10 (vm_brk (m_vmmaps model))) (v_addi pc 4) mem rom) model) K ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
intros regs pc mem rom model w K HF HE Hh H17 H10 Hc.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
assert (H0 : ms_gpr ms 0 = Z_to_bv 64 0) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = vm_brk (m_vmmaps model)).
{ intros r. rewrite H0. unfold brk_resolution_ok, Mmap.brk_r_ok. cbv zeta.
unfold w_is0. rewrite bv_eqb_refl. cbn [orb]. apply bv_eqb_eq. }
assert (Hq : brk_resolution_ok model (ms_gpr ms 0) (vm_brk (m_vmmaps model))) by (apply Hcases; reflexivity).
apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_resolution_ok model (ms_gpr ms 0) r} => K)));
[| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hq); exact Ht]].
eapply srz_cases; [exact (exist _ _ Hq)
| exact (node_brk_lazy ms model (getr regs 17) (fun r => brk_resolution_ok model (ms_gpr ms 0) r) Hh eq_refl Hno
(fun r Hr => Hr) (brk_ns_unique ms model (getr regs 17) _ Hno Hcases) (fun r Hr => or_introl Hr)) |].
intros [r Hr]. cbn [proj1_sig].
pose proof (proj1 (Hcases r) Hr) as Er. subst r.
rewrite H0, brk_zeros_query, brk_unmaps_keep.
rewrite (brk_model_query _ model eq_refl), vmmaps_eta, with_vmmaps_eta.
unfold ms. rewrite adv_ret_epend. exact Hc.
Qed.

Lemma srz_brk_grow_lazy : forall regs (pc : word) mem rom model w (d : Z) KB,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 214 ->
let h := m_vmmaps model in
let b := vm_brk h in
(bv_unsigned b mod page_size = 0)%Z -> (d mod page_size = 0)%Z -> (0 < d)%Z ->
(0 < bv_unsigned b)%Z -> (bv_unsigned b + d < 2 ^ 64)%Z ->
(bv_unsigned (vm_start_brk h) <= bv_unsigned b + d)%Z ->
getr regs 10 = Z_to_bv 64 (bv_unsigned b + d) ->
Mmap.brk_grow_ok model (Z_to_bv 64 (bv_unsigned b + d)) (Z_to_bv 64 (bv_unsigned b + d)) = true ->

srealizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (bv_unsigned b + d))) (v_addi pc 4)
(zfill b (Z_to_bv 64 d) mem) rom)
(with_vmmaps (mkVmMapsFull (vm_reserved h) ((b, Z_to_bv 64 d) :: vm_maps h)
(vm_noaccess h) (vm_start_brk h)
(Z_to_bv 64 (bv_unsigned b + d)) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) model)) KB ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
intros regs pc mem rom model w d KB HF HE Hh H17 h b Hbal Hdal Hd Hb0 Hnw Hs H10 Hadm HB.
pose proof (u64_range b) as Hbr.
set (req := Z_to_bv 64 (bv_unsigned b + d)) in *.
assert (Hureq : bv_unsigned req = (bv_unsigned b + d)%Z) by (unfold req; apply u64_lit; lia).
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> (r = b \/ (r = req /\ Mmap.brk_grow_ok model req req = true))).
{ intros r. rewrite H0. apply brk_r_ok_grow_cases; fold h; fold b; rewrite ?Hureq; lia. }
assert (Hgrow : brk_resolution_ok model (ms_gpr ms 0) req) by (apply Hcases; right; split; [reflexivity | exact Hadm]).
assert (Hlt : (bv_unsigned b < bv_unsigned req)%Z) by (rewrite Hureq; lia).
assert (Hreq0 : req <> Z_to_bv 64 0).
{ intros E. apply (f_equal bv_unsigned) in E. rewrite Hureq in E.
change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in E. lia. }
assert (Hw0 : w_is0 req = false) by (unfold w_is0; apply bv_eqb_neq; exact Hreq0).
assert (Hs' : (bv_unsigned (vm_start_brk (m_vmmaps model)) <= bv_unsigned req)%Z) by (fold h; rewrite Hureq; exact Hs).
assert (HPall : forall r, brk_resolution_ok model (ms_gpr ms 0) r -> r = req
\/ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms (getr regs 17)) model
(mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
(brk_unmaps r (vm_brk (m_vmmaps model))) [] [])).
{ intros r Hr. destruct (proj1 (Hcases r) Hr) as [-> | [-> _]]; [right | left; reflexivity].
apply (brk_grow_keep_sp (sys_input segs ms (getr regs 17)) req model);
[exact Hno | exact H0 | exact Hw0 | exact Hs' | exact Hlt | reflexivity | exact Hadm]. }
assert (HPns : forall r, r = req -> ~ spurious_refusal_cfg (alloc_only_cfg false) (sys_input segs ms (getr regs 17)) model
(mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
(brk_unmaps r (vm_brk (m_vmmaps model))) [] [])).
{ intros r ->. apply (brk_grow_grant_ns (sys_input segs ms (getr regs 17)) req model);
[exact Hno | exact H0 | exact Hw0 | exact Hs' | exact Hlt | reflexivity]. }
assert (HPok : forall r, r = req -> brk_resolution_ok model (ms_gpr ms 0) r) by (intros r ->; exact Hgrow).
apply (srz_conseq segs _ (t_alt (fun _ : {r : word | r = req} => KB)));
[| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist (fun r => r = req) req eq_refl); exact Ht]].
eapply srz_cases; [exact (exist (fun r => r = req) req eq_refl)
| exact (node_brk_lazy ms model (getr regs 17) (fun r => r = req) Hh eq_refl Hno HPok HPns HPall) |].
intros [r Er]. cbn [proj1_sig]. fold h. subst r.
rewrite H0. fold b. rewrite (brk_zeros_grow req req b Hreq0 Hb0 Hlt), (brk_unmaps_grow req b) by lia.
unfold brk_page_range.
rewrite (page_round_up_Z_aligned (bv_unsigned b)) by (first [lia | exact Hbal]).
rewrite (page_round_up_Z_aligned (bv_unsigned req))
by (rewrite Hureq; first [lia | rewrite Z.add_mod, Hbal, Hdal by (unfold page_size; lia); reflexivity]).
rewrite (proj2 (Z.ltb_lt _ _) Hlt).
replace (Z_to_bv 64 (bv_unsigned b)) with b by (symmetry; apply Z_to_bv_u_eq'; reflexivity).
rewrite Hureq. replace (bv_unsigned b + d - bv_unsigned b)%Z with d by lia.
unfold req, b, h. rewrite (brk_model_grow_eq model d) by assumption.
unfold ms. rewrite adv_zeros1_epend. exact HB.
Qed.

Lemma srz_brk_grow_blocked_lazy : forall regs (pc : word) mem rom model w (req : word) KA,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 214 ->
let h := m_vmmaps model in
let b := vm_brk h in
getr regs 10 = req ->
(0 < bv_unsigned req)%Z ->
(bv_unsigned (vm_start_brk h) <= bv_unsigned req)%Z ->
(bv_unsigned b <= bv_unsigned req)%Z ->
Mmap.brk_grow_ok model req req = false ->
srealizes segs (mkCfg (mkst (regupd regs 10 b) (v_addi pc 4) mem rom) model) KA ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) KA.
Proof.
intros regs pc mem rom model w req KA HF HE Hh H17 h b H10 Hpos Hs Hb Hblk HA.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 214%Z) by (rewrite H17; apply u64_lit; lia).
assert (H0 : ms_gpr ms 0 = req) by (unfold ms; rewrite ms_gpr_epend0; exact H10).
assert (Hcases : forall r, brk_resolution_ok model (ms_gpr ms 0) r <-> r = b).
{ intros r. rewrite H0, (brk_r_ok_grow_cases model req r Hpos Hs Hb). fold h. fold b. split.
- intros [-> | [-> Hg]]; [reflexivity | rewrite Hblk in Hg; discriminate].
- intros ->. left. reflexivity. }
assert (Hkeep : brk_resolution_ok model (ms_gpr ms 0) b) by (apply Hcases; reflexivity).
apply (srz_conseq segs _ (t_alt (fun _ : {r : word | brk_resolution_ok model (ms_gpr ms 0) r} => KA)));
[| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ _ Hkeep); exact Ht]].
eapply srz_cases; [exact (exist _ b Hkeep)
| exact (node_brk_lazy ms model (getr regs 17) (fun r => brk_resolution_ok model (ms_gpr ms 0) r) Hh eq_refl Hno
(fun r Hr => Hr) (brk_ns_unique ms model (getr regs 17) _ Hno Hcases) (fun r Hr => or_introl Hr)) |].
intros [r Hr]. cbn [proj1_sig]. fold h.
pose proof (proj1 (Hcases r) Hr) as Er. subst r. fold b.
rewrite brk_zeros_keep, brk_unmaps_keep. unfold b, h. rewrite brk_model_keep.
unfold ms. rewrite adv_ret_epend. exact HA.
Qed.

Lemma node_set_tid_lazy : forall ms model x8,
m_halted model = None ->
ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 96%Z ->
m_tid model = None ->
node_ok segs (mkCfg ms model) tid_I (fun _ => [])
(fun i => mkCfg (advance_past_svc (apply_effect ms (mkEffectU (proj1_sig i) [] [] [] [] [])))
(with_tid (proj1_sig i) model)).
Proof.
intros ms model x8 Hh Hsvc Hno Htid.
assert (Hchk : forall eff, check_syscall (sys_input segs ms x8) eff model =
match eff with
| mkEffectU ret [] [] [] [] [] =>
if ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool
then CheckOk (with_tid ret model) [] else CheckReject
| _ => CheckReject end).
{ intros eff. rewrite (check_syscall_96 segs ms x8 eff model Hno). unfold check_set_tid_address. rewrite Htid. reflexivity. }
apply (node_chk_noacc ms model x8 tid_I
(fun i => mkEffectU (proj1_sig i) [] [] [] [] [])
(fun i => with_tid (proj1_sig i) model) Hh Hsvc).
- intros [t [Ht1 Ht2]]. cbn [proj1_sig]. rewrite Hchk.
rewrite (proj2 (Z.ltb_lt _ _) Ht1), (proj2 (Z.ltb_lt _ _) Ht2). reflexivity.
- intros i. apply (ns_sysno_eq _ _ _ 96%Z); [exact Hno | reflexivity].
- intros [ret ws zs us cs ci] m' ev Hc. left. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool eqn:Eb; [|discriminate].
apply andb_true_iff in Eb as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2.
injection Hc as <- <-. exists (exist _ ret (conj E1 E2)). repeat split; reflexivity.
- intros [ret ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct zs; [|discriminate]. destruct us; [|discriminate].
destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct ((0 <? bv_unsigned ret)%Z && (bv_unsigned ret <? PID_MAX_ENVELOPE)%Z)%bool; discriminate.
- intros [t Ht]. cbn [proj1_sig]. rewrite with_tid_halted. exact Hh.
- intros [t Ht]. reflexivity.
Qed.

Lemma srz_set_tid_lazy : forall regs (pc : word) mem rom model K w,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 96 ->
m_tid model = None ->
(forall tid, (0 < bv_unsigned tid < PID_MAX_ENVELOPE)%Z ->
srealizes segs (mkCfg (mkst (regupd regs 10 tid) (v_addi pc 4) mem rom) (with_tid tid model)) K) ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) K.
Proof.
intros regs pc mem rom model K w HF HE Hh H17 Htid Hk.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
apply (srz_conseq segs _ (t_alt (fun _ : tid_I => K)));
[| intros tr; split; [intros [_ Ht]; exact Ht | intros Ht; exists (exist _ (Z_to_bv 64 1) one_tid_ok); exact Ht]].
eapply srz_cases; [exact (exist _ (Z_to_bv 64 1) one_tid_ok)
| eapply node_set_tid_lazy; [exact Hh | reflexivity | rewrite H17; apply u64_lit; lia | exact Htid] |].
intros [t Ht]. cbn [proj1_sig].
change (mkEffectU t [] [] [] [] []) with (mkEffect t [] []).
rewrite apply_effect_no_write, adv_set_epend. apply Hk. exact Ht.
Qed.

Lemma srz_exit_at_lazy : forall regs (pc : word) mem rom model w code,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
(getr regs 17 = Z_to_bv 64 94 \/ getr regs 17 = Z_to_bv 64 93) ->
getr regs 10 = code ->
srealizes segs (mkCfg (mkst regs pc mem rom) model)
(t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
intros regs pc mem rom model w code HF HE Hh H17 H10.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
rewrite <- H10, <- (ms_gpr_epend0 regs pc mem rom (getr regs 17)).
eapply srz_exit; [exact Hh | reflexivity |].
destruct H17 as [H|H]; [right|left]; rewrite H; reflexivity.
Qed.

Lemma mmap_gates_core50 : forall flags prot,
mmap_flags_core flags = 50%Z ->
mmap_modeled_b prot flags (Z_to_bv 64 0) = false
/\ mmap_noaccess_b prot flags (Z_to_bv 64 0) = false
/\ mmap_fixed_noaccess_b (Z_to_bv 64 0) flags (Z_to_bv 64 0) = true
/\ mmap_fixed_noaccess_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = false
/\ mmap_fixed_rw_b (Z_to_bv 64 3) flags (Z_to_bv 64 0) = true.
Proof.
intros flags prot Hc. unfold mmap_modeled_b, mmap_noaccess_b, mmap_fixed_noaccess_b, mmap_fixed_rw_b.
rewrite Hc. repeat split; try (vm_compute; reflexivity).
all: destruct (bv_unsigned prot =? _)%Z; vm_compute; reflexivity.
Qed.

Definition fixedin_ok_vmmaps (prot : Z) (addr n : word) (h : VmMaps) : VmMaps :=
if Z.eqb prot 0
then mkVmMapsFull (vm_reserved h) (vm_maps h)
((addr, n) :: maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
else mmap_fixed_rw_next h addr n.

Definition fixedin_destroyed_vmmaps (addr n : word) (h : VmMaps) : VmMaps :=
mkVmMapsFull (vm_reserved h)
(maps_subtract (vm_maps h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(maps_subtract (vm_noaccess h) (bv_unsigned addr) (bv_unsigned addr + bv_unsigned n))
(vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).

Definition fixedin_ok_model (prot : Z) (flags addr n : word) (m : Model) : Model :=
with_mmap_replacement flags addr n (with_vmmaps (fixedin_ok_vmmaps prot addr n (m_vmmaps m)) m).
Definition fixedin_destroyed_model (addr n : word) (m : Model) : Model :=
with_mmap_destroyed addr n (fixedin_destroyed_vmmaps addr n (m_vmmaps m)) m.

Definition fixedin_ok_eff (prot : Z) (addr n : word) : SyscallEffect :=
if Z.eqb prot 0 then mkEffectU addr [] [] [(addr, n)] [] [] else mkEffectU addr [] [(addr, n)] [] [] [].

Lemma with_mmap_replacement_halted' : forall flags a n m,
m_halted (with_mmap_replacement flags a n m) = m_halted m.
Proof.
intros. unfold with_mmap_replacement, with_mmap_backing, vm_forget_range.
destruct (mmap_noreserve_b flags); reflexivity.
Qed.

Lemma mmap_fixedin_check : forall ms x8 model eff (prot : Z) (flags addr : word) (len : Z),
bv_unsigned x8 = 222%Z ->
(prot = 0 \/ prot = 3)%Z ->
mmap_flags_core flags = 50%Z ->
ms_gpr ms 0 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
ms_gpr ms 1 = Z_to_bv 64 len -> (0 < len)%Z ->
ms_gpr ms 2 = Z_to_bv 64 prot -> ms_gpr ms 3 = flags ->
ms_gpr ms 4 = Z_to_bv 64 (-1) -> ms_gpr ms 5 = Z_to_bv 64 0 ->
(bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
(prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
check_syscall (sys_input segs ms x8) eff model
= match eff with
| mkEffectU r [] zs us [] [] =>
if errno_ret_in mmap_errnos r
then match zs with
| [] => match us with
| [] => CheckOk model []
| _ => if listNN_eqb us [(addr, n)]
then CheckOk (fixedin_destroyed_model addr n model) []
else CheckReject
end
| _ => CheckReject
end
else if (Z.eqb prot 0)
then match zs with
| [] => if bv_eqb r addr && listNN_eqb us [(addr, n)]
then CheckOk (fixedin_ok_model prot flags addr n model) []
else CheckReject
| _ => CheckReject
end
else match us with
| [] => if bv_eqb r addr && listNN_eqb zs [(addr, n)]
then CheckOk (fixedin_ok_model prot flags addr n model) []
else CheckReject
| _ => CheckReject
end
| _ => CheckReject
end.
Proof.
intros ms x8 model eff prot flags addr len Hno Hprot Hcore H0 Hal Hpos H1 Hlen H2 H3 H4 H5 Hce n Hrf Hmc Hbud.
pose proof (alloc_top_lt (m_vmmaps model)) as Hcv. unfold two_pow_64 in Hcv.
assert (Hlen' : (len < 2 ^ 64)%Z).
{ pose proof (page_round_up_Z_bounds len ltac:(lia)). pose proof (u64_range addr). lia. }
assert (Hu1 : bv_unsigned (ms_gpr ms 1) = len) by (rewrite H1; apply u64_lit; lia).
rewrite (mmap_check segs ms x8 model eff Hno). unfold check_mmap.
assert (E1 : w_is0 (ms_gpr ms 1) = false).
{ unfold w_is0. apply bv_eqb_neq. intros Hz. rewrite Hz in Hu1. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z in Hu1. lia. }
rewrite E1, H2, H3, H5, H0, Hu1.
destruct (mmap_gates_core50 flags (Z_to_bv 64 prot) Hcore) as (G1 & G2 & G3 & G4 & G5).
rewrite G1, G2, mmap_off_aligned_b_0, (mmap_anon_b_of_core flags _ Hcore eq_refl). cbn [negb].
pose proof (u64_range addr) as Har.
destruct Hprot as [-> | ->].
-
rewrite G3. cbv beta iota zeta.
rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
rewrite (proj2 (Z.leb_le _ _) Hce). cbn [negb].
rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct cs; [|destruct zs; destruct us; reflexivity].
destruct ci; [|destruct zs; destruct us; reflexivity].
destruct zs; [|destruct (errno_ret_in mmap_errnos r); destruct us; reflexivity].
reflexivity.
-
rewrite G4, G5. cbv beta iota zeta.
rewrite (proj2 (Z.leb_gt _ _)) by (unfold two_pow_64; lia).
rewrite (proj2 (Z.leb_le _ _) Hce). cbn [negb].
rewrite (proj2 (Z.eqb_eq _ _) Hal). cbn [negb].
rewrite (proj2 (Z.ltb_lt _ _) Hpos). cbn [negb]. fold n. rewrite Hrf, Hmc. cbn [andb Z.eqb].
rewrite (Hbud eq_refl).
destruct eff as [r ws zs us cs ci]. destruct ws; [|reflexivity].
destruct cs; [|destruct zs; destruct us; reflexivity].
destruct ci; [|destruct zs; destruct us; reflexivity].
destruct (errno_ret_in mmap_errnos r); [destruct zs; reflexivity|].
destruct us; [|reflexivity]. rewrite andb_true_r. reflexivity.
Qed.

Lemma srz_mmap_fixedin_lazy : forall regs (pc : word) mem rom model w (prot : Z) (flags addr : word) (len : Z) KB,
fetch_word segs pc = Some w -> is_ecall w = true ->
m_halted model = None ->
getr regs 17 = Z_to_bv 64 222 ->
(prot = 0 \/ prot = 3)%Z -> mmap_flags_core flags = 50%Z ->
getr regs 10 = addr -> (bv_unsigned addr mod page_size = 0)%Z -> (0 < bv_unsigned addr)%Z ->
getr regs 11 = Z_to_bv 64 len -> (0 < len)%Z ->
(bv_unsigned addr + page_round_up_Z len <= alloc_top (m_vmmaps model))%Z ->
getr regs 12 = Z_to_bv 64 prot -> getr regs 13 = flags ->
getr regs 14 = Z_to_bv 64 (-1) -> getr regs 15 = Z_to_bv 64 0 ->
let n := Z_to_bv 64 (page_round_up_Z len) in
region_free (vm_reserved (m_vmmaps model)) addr n = true ->
map_contains (vm_maps (m_vmmaps model)) addr n = true ->
(prot = 3%Z -> mmap_fixed_rw_budget_ok flags model addr n = true) ->
srealizes segs (mkCfg (mkst (regupd regs 10 addr) (v_addi pc 4)
(if Z.eqb prot 0 then unfill addr n mem else zfill addr n mem) rom)
(fixedin_ok_model prot flags addr n model)) KB ->
srealizes segs (mkCfg (mkst regs pc mem rom) model) KB.
Proof.
intros regs pc mem rom model w prot flags addr len KB HF HE Hh H17 Hprot Hcore H10 Hal Hpos H11 Hlen Hce H12 H13 H14 H15 n Hrf Hmc Hbud HB.
pose proof (alloc_top_lt (m_vmmaps model)) as Hcv. unfold two_pow_64 in Hcv. pose proof (u64_range addr) as Har.
eapply srz_sys_lazy; [exact Hh | exact HF | exact HE |].
set (ms := epend regs pc mem rom (getr regs 17)).
assert (Hno : bv_unsigned (getr regs 17) = 222%Z) by (rewrite H17; apply u64_lit; lia).
assert (Hlen' : (len < 2 ^ 64)%Z) by (pose proof (page_round_up_Z_bounds len ltac:(lia)); lia).
pose proof (fun eff => mmap_fixedin_check ms (getr regs 17) model eff prot flags addr len Hno Hprot Hcore
ltac:(unfold ms; rewrite ms_gpr_epend0; exact H10) Hal Hpos
ltac:(unfold ms; rewrite ms_gpr_epend1; exact H11) Hlen
ltac:(unfold ms; rewrite ms_gpr_epend2; exact H12)
ltac:(unfold ms; rewrite ms_gpr_epend3; exact H13)
ltac:(unfold ms; rewrite ms_gpr_epend4; exact H14)
ltac:(unfold ms; rewrite ms_gpr_epend5; exact H15)
Hce Hrf Hmc Hbud) as Hchk.
cbv zeta in Hchk. fold n in Hchk.
assert (Hp0 : Z.eqb prot 0 = true <-> prot = 0%Z) by (apply Z.eqb_eq).
assert (Hnr0 : errno_ret_in mmap_errnos addr = false)
by (apply (mmap_errnos_below_top addr (m_vmmaps model) (page_round_up_Z len)); [apply page_round_up_Z_nonneg; lia | exact Hce]).
assert (Hok0 : check_syscall (sys_input segs ms (getr regs 17)) (fixedin_ok_eff prot addr n) model
= CheckOk (fixedin_ok_model prot flags addr n model) []).
{ unfold fixedin_ok_eff. destruct (Z.eqb prot 0) eqn:Ep;
rewrite Hchk, Hnr0, ?Ep, bv_eqb_refl, (proj2 (listNN_eqb_eq _ _) eq_refl); reflexivity. }
assert (Hnr1 : errno_ret_in mmap_errnos (eff_ret (fixedin_ok_eff prot addr n)) = false)
by (unfold fixedin_ok_eff; destruct (Z.eqb prot 0); exact Hnr0).
apply (srz_det_noacc ms model (getr regs 17) (fixedin_ok_eff prot addr n) (fixedin_ok_model prot flags addr n model) KB Hh eq_refl Hok0).
- apply ns_mmap_ret; [exact Hno | exact Hnr1].
- intros eff m' evs. rewrite Hchk. intros Hc. destruct eff as [r ws zs us cs ci].
destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r) eqn:Er.
{ right. split; [eapply sp_mmap_of_ok; [exact Hno | exact Er | exact Hok0 | exact Hnr1]|].
destruct zs; [|discriminate]. destruct us as [|u us]; [injection Hc as <- <-; exact Hh|].
destruct (listNN_eqb (u :: us) [(addr, n)]); [|discriminate]. injection Hc as <- <-.
unfold fixedin_destroyed_model, with_mmap_destroyed. rewrite vm_forget_range_halted, with_vmmaps_halted. exact Hh. }
left. unfold fixedin_ok_eff.
destruct (Z.eqb prot 0) eqn:Ep.
* destruct zs; [|discriminate].
destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
destruct (listNN_eqb us [(addr, n)]) eqn:Hl; [|discriminate].
apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-. repeat split; reflexivity.
* destruct us; [|discriminate].
destruct (bv_eqb r addr) eqn:Eb; [|discriminate].
destruct (listNN_eqb zs [(addr, n)]) eqn:Hl; [|discriminate].
apply bv_eqb_eq in Eb. apply listNN_eqb_eq in Hl. subst. injection Hc as <- <-. repeat split; reflexivity.
- intros [r ws zs us cs ci] Hc. rewrite Hchk in Hc.
destruct ws; [|discriminate]. destruct cs; [|discriminate]. destruct ci; [|discriminate].
destruct (errno_ret_in mmap_errnos r).
{ destruct zs; [|discriminate]. destruct us; [discriminate|]. destruct (listNN_eqb _ _); discriminate. }
destruct (Z.eqb prot 0); [destruct zs; [|discriminate] | destruct us; [|discriminate]];
destruct (bv_eqb r addr && listNN_eqb _ _)%bool; discriminate.
- unfold fixedin_ok_model; rewrite with_mmap_replacement_halted', with_vmmaps_halted; exact Hh.
- unfold fixedin_ok_eff; destruct (Z.eqb prot 0); reflexivity.
- unfold ms, fixedin_ok_eff. destruct (Z.eqb prot 0).
+ rewrite adv_unmaps1_epend. exact HB.
+ rewrite adv_zeros1_epend. exact HB.
Qed.

End Noacc.

Open Scope Z_scope.
Import AX2 AX2S AP APS.

Lemma is_ecall_at_sound : forall SEGS cs,
is_ecall_at SEGS cs = true ->
0 <= pc cs /\ pc cs + 4 < two64 /\
exists w, fetch_word SEGS (Z_to_bv 64 (pc cs)) = Some w /\ is_ecall w = true.
Proof.
intros SEGS cs H. unfold is_ecall_at in H.
apply andb_prop in H as [H Hf]. apply andb_prop in H as [H0 H4].
apply Z.leb_le in H0. apply Z.ltb_lt in H4.
destruct (fetch_word SEGS (Z_to_bv 64 (pc cs))) as [w|] eqn:Hw; [|discriminate].
repeat split; try assumption. exists w. auto.
Qed.

Lemma bv_and_255 : forall c0, 0 <= c0 < two64 ->
bv_and (Z_to_bv 64 c0) (Z_to_bv 64 255) = Z_to_bv 64 (Z.land c0 255).
Proof.
intros c0 Hc. apply bv_eq. rewrite bv_and_unsigned, !u64_lit by (unfold two64 in *; lia).
change 255%Z with (Z.ones 8). rewrite Z.land_ones by lia.
symmetry. apply u64_lit. unfold two64 in *.
pose proof (Z.mod_pos_bound c0 (2 ^ 8) ltac:(lia)). lia.
Qed.

Lemma Some_inj : forall {T : Type} (a b : T), Some a = Some b -> a = b.
Proof. intros T a b H. congruence. Qed.

Lemma v_addi_pc : forall p, 0 <= p -> p + 4 < two64 ->
v_addi (Z_to_bv 64 p) 4 = Z_to_bv 64 (p + 4).
Proof.
intros p H0 H4. unfold v_addi. f_equal. unfold two64 in *. rewrite u64_lit by lia. reflexivity.
Qed.

Section CsOk.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable USP : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.

End CsOk.
